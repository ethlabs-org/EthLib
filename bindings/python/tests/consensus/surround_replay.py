"""Store-level replay: an honest validator's two votes form a surround pair (phase0, minimal).

Run as a module: python -m tests.consensus.surround_replay --v 0 [--fork altair] [--control]
(from bindings/python); test_honest_surround.py asserts its outcome.

Everything is executed by EthLib's compiled specification through the Python bindings:
- genesis: initialize_beacon_state_from_eth1 on 100 BLS-signed deposits (checks on);
- blocks: state_transition with every signature checked; state roots computed by EthLib;
- committees, proposers, attestation data and signatures: EthLib's honest-validator exports;
- the store: one consensus.fork_choice run (getForkchoiceStore, onTick, onBlockWithVotes,
  onAttestation, getHead) with BLS checks on, from the genesis anchor;
- the honest votes: consensus.api_attestation_data on that store (getHead, head state,
  process_slots to the duty slot, get_attestation_data), cross-checked by recomputing the
  same chain by hand from the head returned by the store.
"""

from __future__ import annotations

import argparse
import json
import sys

from . import surround_builders as cx
from .surround_builders import (
    CONFIG,
    PRESET,
    SLOT_SECONDS,
    SPE,
    advance,
    aggregate,
    attestation_data,
    committees,
    consensus,
    data_json,
    deposits as make_deposits,
    genesis_block,
    hx,
    is_slashable,
    make_block,
    proposer,
    signed_exit,
    state_json,
    unhx,
)

N = 100
EXITERS = [97, 98, 99]  # voluntary exits signed at epoch 64 -> exit_epoch 69 = r + 1
R = 68  # r: the epoch of the two competing branches
X_SLOT, Q_SLOT, P_SLOT = 64 * SPE + 1, 66 * SPE + 7, 67 * SPE + 7  # 513, 535, 543
C_SLOT, B_SLOT = R * SPE + 1, R * SPE + 7  # 545, 551
D_SLOT = (R + 1) * SPE + 1  # 553 (control only)
B_PARTICIPANTS = 66  # 3*66 = 198 < 200 = 2*100, but 198 >= 194 = 2*97
C_VOTERS = 5


def block_root_phase0(message: bytes) -> bytes:
    return consensus.ssz_static(PRESET, "phase0", "BeaconBlock", message)[0]


def committee_of(state_at_epoch: bytes, epoch: int, validator: int) -> tuple[int, int]:
    """(slot, committee index) of a validator in an epoch, by EthLib's get_committee_assignment."""
    found = consensus.get_committee_assignment(
        PRESET, cx.FORK, state_at_epoch, epoch, validator, cx.OVERRIDES
    )
    assert found is not None
    _, index, slot = found
    return slot, index


def slot_votes(head_post: bytes, head_root: bytes, head_slot: int, slots, include) -> list[bytes]:
    """Aggregates, one per committee and slot, of the included members' honest-looking votes."""
    out = []
    cache: dict[int, list[dict]] = {}
    for t in slots:
        st = advance(head_post, t)
        epoch = t // SPE
        if epoch not in cache:
            cache[epoch] = committees(st, epoch)
        for com in cache[epoch]:
            if int(com["slot"]) != t:
                continue
            members = [int(x) for x in com["validators"] if include(int(x))]
            if members:
                data = attestation_data(st, head_root, head_slot, int(com["index"]))
                out.append(aggregate(st, data, members))
    return out


def proposers_of(chain_post: bytes, epoch: int) -> set[int]:
    return {proposer(advance(chain_post, t), N) for t in range(epoch * SPE, (epoch + 1) * SPE)}


def build(v: int | None, control: bool, fork: str = "phase0") -> dict:
    # Altair: the chain launches at phase0 and upgrades at epoch 1 (the only replaced value).
    cx.use(fork, None if fork == "phase0" else {"ALTAIR_FORK_EPOCH": 1})
    deposits = make_deposits(N)
    eth1_time = CONFIG["MIN_GENESIS_TIME"] - CONFIG["GENESIS_DELAY"]
    genesis = consensus.initialize_genesis(
        PRESET, "phase0", b"\x42" * 32, eth1_time, deposits, verify=True, config=cx.OVERRIDES
    )
    assert consensus.is_valid_genesis_state(PRESET, "phase0", genesis, cx.OVERRIDES)
    genesis_root = block_root_phase0(genesis_block(genesis))
    anchor_signed = None
    if fork == "phase0":
        g, gb, g_root = genesis, genesis_block(genesis), genesis_root
    else:
        # The anchor is the first block (slot 16, the start of epoch 2) and its post-state.
        # The run from genesis to it upgrades to Altair at slot 8 inside the slot processing.
        at8 = consensus.process_slots(PRESET, "phase0", genesis, SPE, cx.OVERRIDES)
        upgraded = consensus.upgrade_state(PRESET, fork, at8, True, cx.OVERRIDES)
        anchor_signed, g_root, g = make_block(upgraded, genesis_root, 2 * SPE, N)
        across = consensus.state_transition_across(
            PRESET, "phase0", genesis, fork, anchor_signed, True, cx.OVERRIDES
        )
        assert across == g
        gb = cx.to_ssz("BeaconBlock", cx.to_json("SignedBeaconBlock", anchor_signed)["message"])
    gt = int(state_json(g)["genesis_time"])
    honest = (lambda x: x != v) if v is not None else (lambda x: True)

    steps: list = []
    marks: dict[str, int] = {}

    def tick(slot: int, offset: int = 0) -> None:
        steps.append(("tick", gt + slot * SLOT_SECONDS + offset))

    def mark(name: str) -> None:
        steps.append(("checks", (False, True, None)))
        marks[name] = len(steps) - 1

    # Common prefix: exits at epoch 64, full votes in epochs 66 and 67.
    exits = [signed_exit(advance(g, X_SLOT), i, 64) for i in EXITERS]
    x_block, x_root, x_post = make_block(g, g_root, X_SLOT, N, exits=exits)
    q_votes = slot_votes(x_post, x_root, X_SLOT, range(66 * SPE, Q_SLOT), honest)
    q_block, q_root, q_post = make_block(x_post, x_root, Q_SLOT, N, attestations=q_votes)
    p_votes = slot_votes(q_post, q_root, Q_SLOT, range(67 * SPE, P_SLOT), honest)
    p_block, p_root, p_post = make_block(q_post, q_root, P_SLOT, N, attestations=p_votes)

    # Branch B: 66 epoch-r target votes. Branch C: an empty block on a different slot.
    chosen: list[int] = []
    for t in range(R * SPE, B_SLOT):
        st = advance(p_post, t)
        for com in committees(st, R):
            if int(com["slot"]) == t:
                chosen += [
                    int(x) for x in com["validators"] if int(x) not in EXITERS and honest(int(x))
                ]
    assert len(chosen) >= B_PARTICIPANTS, len(chosen)
    participants = set(chosen[:B_PARTICIPANTS])
    b_votes = slot_votes(
        p_post, p_root, P_SLOT, range(R * SPE, B_SLOT), lambda x: x in participants
    )
    c_block, c_root, c_post = make_block(p_post, p_root, C_SLOT, N, graffiti=b"C" * 32)
    b_block, b_root, b_post = make_block(
        p_post, p_root, B_SLOT, N, attestations=b_votes, graffiti=b"B" * 32
    )

    for slot, block in ((X_SLOT, x_block), (Q_SLOT, q_block), (P_SLOT, p_block)):
        tick(slot)
        steps.append(("block", block))
    tick(R * SPE)
    mark("epoch r start (common prefix imported)")
    tick(C_SLOT)
    steps.append(("block", c_block))
    tick(B_SLOT)
    steps.append(("block", b_block))

    # One epoch r+1 vote for B gives it the initial LMD lead.
    b69 = advance(b_post, (R + 1) * SPE)
    w1 = next(int(x) for com in committees(b69, R + 1) for x in com["validators"] if honest(int(x)))
    s1, i1 = committee_of(b69, R + 1, w1)
    st1 = advance(b_post, s1)
    w1_vote = aggregate(st1, attestation_data(st1, b_root, B_SLOT, i1), [w1])
    tick(s1 + 1)
    steps.append(("attestation", w1_vote))

    d_root = None
    if control:
        d_block, d_root, _ = make_block(b_post, b_root, D_SLOT, N, graffiti=b"D" * 32)
        tick(max(D_SLOT, s1 + 1))
        steps.append(("block", d_block))

    result = {
        "v": v,
        "w1": w1,
        "exiters": EXITERS,
        "b_participants": sorted(participants),
        "roots": {
            "genesis": hx(g_root),
            "X": hx(x_root),
            "Q": hx(q_root),
            "P": hx(p_root),
            "B": hx(b_root),
            "C": hx(c_root),
            **({"D": hx(d_root)} if d_root else {}),
        },
        "slots": {"X": X_SLOT, "Q": Q_SLOT, "P": P_SLOT, "B": B_SLOT, "C": C_SLOT},
    }
    result["proposers"] = {
        "epoch r+1 (B)": sorted(proposers_of(b_post, R + 1)),
        "epoch r+2 (B)": sorted(proposers_of(b_post, R + 2)),
        "epoch r+3 (C)": sorted(proposers_of(c_post, R + 3)),
        "epoch r+3 (B)": sorted(proposers_of(b_post, R + 3)),
    }
    if v is None:
        return result

    def honest_vote(epoch: int, chain_post: bytes, label: str) -> tuple[dict, int, int, int]:
        """Tick to v's duty slot, read the store, and build v's vote from the store."""
        slot, index = committee_of(advance(chain_post, epoch * SPE), epoch, v)
        # The export ticks in whole seconds: one second into the slot is before the attestation
        # deadline (1999 ms) and in the same slot, so the store equals the store at the deadline.
        tick(slot, 1)
        mark(label)
        api = consensus.api_attestation_data(
            PRESET, cx.FORK, g, gb, steps, slot, index, verify=True
        )
        return api["data"], slot, index, len(steps)

    # Vote a: duty in epoch r+2, head B (no B descendant crossing r+1 -> r+2 imported).
    a_api, s_a, i_a, a_prefix = honest_vote(R + 2, b_post, "vote a (epoch r+2 duty)")

    # Received votes for C from other validators at their epoch r+2 duties.
    c70 = advance(c_post, (R + 2) * SPE)
    c_voters = [
        int(x)
        for com in committees(c70, R + 2)
        for x in com["validators"]
        if honest(int(x)) and int(x) != w1
    ][:C_VOTERS]
    c_votes = []
    for x in c_voters:
        sx, ix = committee_of(c70, R + 2, x)
        stx = advance(c_post, sx)
        c_votes.append(aggregate(stx, attestation_data(stx, c_root, C_SLOT, ix), [x]))
    # v's own vote a reaches its store as well.
    st_a = advance(b_post, s_a)
    a_ssz = attestation_data(st_a, b_root, B_SLOT, i_a)
    tick((R + 3) * SPE)
    a_att = aggregate(st_a, a_ssz, [v])
    steps.append(("attestation", a_att))
    for vote in c_votes:
        steps.append(("attestation", vote))

    # Vote b: duty in epoch r+3.
    b_chain = c_post if not control else b_post
    b_api, s_b, i_b, b_prefix = honest_vote(R + 3, b_chain, "vote b (epoch r+3 duty)")
    b_att = None
    if not control:
        # v signs and sends vote b; the store's own onAttestation accepts it as a valid message.
        st_b = advance(c_post, s_b)
        b_att = aggregate(st_b, attestation_data(st_b, c_root, C_SLOT, i_b), [v])
        tick(s_b + 1)
        steps.append(("attestation", b_att))

    outcomes = consensus.fork_choice(PRESET, cx.FORK, g, gb, steps, True, cx.OVERRIDES)
    assert len(outcomes) == len(steps)
    failures = [
        (k, steps[k][0], o)
        for k, o in enumerate(outcomes)
        if steps[k][0] != "checks" and o is not None
    ]
    assert not failures, failures

    def read(name: str) -> dict:
        o = outcomes[marks[name]]
        return {
            "time_slot": (o["time_ms"] // 1000 - gt) // SLOT_SECONDS,
            "head": {"slot": o["head"]["slot"], "root": hx(o["head"]["root"])},
            "justified": {
                "epoch": o["justified_checkpoint"]["epoch"],
                "root": hx(o["justified_checkpoint"]["root"]),
            },
            "finalized": {
                "epoch": o["finalized_checkpoint"]["epoch"],
                "root": hx(o["finalized_checkpoint"]["root"]),
            },
            "proposer_boost_root": hx(o["proposer_boost_root"]),
            "viable_leaves": sorted(
                (hx(e["root"]), e["weight"]) for e in o["viable_for_head_roots_and_weights"]
            ),
        }

    # Recompute each vote by hand from the head the store returned (HonestVoteData chain).
    posts = {hx(b_root): (b_post, B_SLOT), hx(c_root): (c_post, C_SLOT)}

    def by_hand(name: str, slot: int, index: int) -> dict:
        head = read(name)["head"]
        post, head_slot = posts[head["root"]]
        assert head_slot == head["slot"]
        st = advance(post, slot)
        return data_json(attestation_data(st, unhx(head["root"]), head_slot, index))

    a_hand = by_hand("vote a (epoch r+2 duty)", s_a, i_a) if not control else None
    b_hand = by_hand("vote b (epoch r+3 duty)", s_b, i_b) if not control else None
    if not control:
        assert a_hand == a_api, (a_hand, a_api)
        assert b_hand == b_api, (b_hand, b_api)

    # Effective balances along both branches: the reference stake does not move before r+1.
    def effective(state: bytes) -> list[int]:
        return sorted({int(x["effective_balance"]) for x in state_json(state)["validators"]})

    result.update(
        {
            "c_voters": c_voters,
            "duties": {
                "a": {"slot": s_a, "committee_index": i_a},
                "b": {"slot": s_b, "committee_index": i_b},
            },
            "reads": {name: read(name) for name in marks},
            "vote_a": a_api,
            "vote_b": b_api,
            "a_slashable_with_b": is_slashable(a_api, b_api) or is_slashable(b_api, a_api),
            "steps": len(steps),
            "step_kinds": [s[0] for s in steps],
            "fork": fork,
            "_raw": {
                "genesis": genesis,
                "anchor": g,
                "anchor_block": gb,
                "anchor_signed": anchor_signed,
                "blocks": {"X": x_block, "Q": q_block, "P": p_block, "C": c_block, "B": b_block},
                "posts": {"X": x_post, "Q": q_post, "P": p_post, "C": c_post, "B": b_post},
                "gossip": {"w1": w1_vote, "c_votes": c_votes, "a": a_att, "b": b_att},
                "steps": steps,
            },
            "effective_balances": {
                "P": effective(p_post),
                "B": effective(b_post),
                "C": effective(c_post),
            },
            "states": {
                "B_justified": state_json(b_post)["current_justified_checkpoint"],
                "C_justified": state_json(c_post)["current_justified_checkpoint"],
                "P_justified": state_json(p_post)["current_justified_checkpoint"],
                "P_finalized": state_json(p_post)["finalized_checkpoint"],
            },
        }
    )
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--v", type=int, default=None)
    parser.add_argument("--control", action="store_true")
    parser.add_argument("--out", default=None)
    parser.add_argument("--fork", default="phase0", choices=["phase0", "altair"])
    args = parser.parse_args()
    result = build(args.v, args.control, args.fork)
    result.pop("_raw", None)
    text = json.dumps(result, indent=1, default=str)
    if args.out:
        open(args.out, "w").write(text)
    print(
        text
        if args.v is None
        else json.dumps(
            {
                k: result[k]
                for k in ("v", "duties", "vote_a", "vote_b", "a_slashable_with_b", "reads")
            },
            indent=1,
        )
    )


if __name__ == "__main__":
    sys.exit(main())
