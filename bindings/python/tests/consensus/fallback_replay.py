"""Store-level replay: a slashing empties the filtered tree, and get_head falls back to J's root.

Run as a module: python -m tests.consensus.fallback_replay --v <index> [--fork altair]
(from bindings/python); test_honest_fallback.py asserts its outcome.

The same harness as surround_replay.py: EthLib's genesis, state transition and fork choice
handlers, with every BLS check on, from a phase0 genesis anchor or an Altair anchor.

- Full votes in epochs 8 and 9 make the store's justified checkpoint 9 at epoch 10.
- Block A (slot 86) carries the epoch-10 target votes of 67 of the 100 validators. Its
  pull-up justifies 10 (3*67 >= 2*100); the store records it and promotes it at epoch 11.
- The honest validator votes at its epoch-11 duty with head A: source 10, target 11.
- Block C (slot 87), A's same-epoch child, carries a valid attester slashing of one of those
  67 voters. Its pull-up sees 66 unslashed voters, 3*66 < 2*100, so C records source 9.
- C is the only leaf. At epoch 12 its voting source 9 is neither the store's 10 nor within two
  epochs, so the filtered tree is empty and get_head returns the justified root, block P.
- The honest validator votes at its epoch-12 duty from P: P's state advanced to that slot has
  source 9, target 12, which surrounds the epoch-11 vote.
"""

from __future__ import annotations

import argparse
import json
import sys

from . import surround_builders as cx
from .surround_builders import (
    PRESET,
    SLOT_SECONDS,
    SPE,
    advance,
    aggregate,
    attestation_data,
    committees,
    consensus,
    data_json,
    hx,
    indexed_vote,
    is_slashable,
    make_block,
    state_json,
    to_ssz,
    unhx,
)
from .surround_replay import N, committee_of, make_anchor, proposers_of, slot_votes

E = 10  # the epoch of blocks A and C
Q_SLOT, P_SLOT = 8 * SPE + 7, 9 * SPE + 7  # 71, 79
A_SLOT, C_SLOT = E * SPE + 6, E * SPE + 7  # 86, 87
VOTERS = 67  # 3*67 = 201 >= 200 = 2*100; one slashed leaves 3*66 = 198 < 200


def build(v: int | None, fork: str = "phase0") -> dict:
    anchor = make_anchor(fork)
    genesis, g, gb, g_root = anchor["genesis"], anchor["state"], anchor["block"], anchor["root"]
    gt = int(state_json(g)["genesis_time"])
    honest = (lambda x: x != v) if v is not None else (lambda x: True)

    steps: list = []
    marks: dict[str, int] = {}

    def tick(slot: int, offset: int = 0) -> None:
        steps.append(("tick", gt + slot * SLOT_SECONDS + offset))

    def mark(name: str) -> None:
        steps.append(("checks", (False, True, None)))
        marks[name] = len(steps) - 1

    # Common prefix: full votes in epochs 8 and 9.
    q_votes = slot_votes(g, g_root, int(state_json(g)["slot"]), range(8 * SPE, Q_SLOT), honest)
    q_block, q_root, q_post = make_block(g, g_root, Q_SLOT, N, attestations=q_votes)
    p_votes = slot_votes(q_post, q_root, Q_SLOT, range(9 * SPE, P_SLOT), honest)
    p_block, p_root, p_post = make_block(q_post, q_root, P_SLOT, N, attestations=p_votes)

    # Block A: 67 epoch-10 target votes from the committees of slots 80 to 85.
    chosen: list[int] = []
    for t in range(E * SPE, A_SLOT):
        st = advance(p_post, t)
        for com in committees(st, E):
            if int(com["slot"]) == t:
                chosen += [int(x) for x in com["validators"] if honest(int(x))]
    assert len(chosen) >= VOTERS, len(chosen)
    voters = set(chosen[:VOTERS])
    a_votes = slot_votes(p_post, p_root, P_SLOT, range(E * SPE, A_SLOT), lambda x: x in voters)
    a_block, a_root, a_post = make_block(p_post, p_root, A_SLOT, N, attestations=a_votes)

    # Block C: A's child, slashing one of A's voters for a double vote at target epoch 10.
    slashed = min(voters)
    s_slot, s_index = committee_of(advance(p_post, E * SPE), E, slashed)
    s_state = advance(p_post, s_slot)
    first = attestation_data(s_state, p_root, P_SLOT, s_index)
    second_doc = data_json(first) | {"beacon_block_root": hx(q_root)}
    second = to_ssz("AttestationData", second_doc)
    slashing = {
        "attestation_1": indexed_vote(s_state, first, slashed),
        "attestation_2": indexed_vote(s_state, second, slashed),
    }
    c_block, c_root, c_post = make_block(
        a_post, a_root, C_SLOT, N, attester_slashings=[slashing], graffiti=b"C" * 32
    )

    result = {
        "fork": fork,
        "v": v,
        "voters": sorted(voters),
        "slashed": slashed,
        "roots": {
            "anchor": hx(g_root),
            "Q": hx(q_root),
            "P": hx(p_root),
            "A": hx(a_root),
            "C": hx(c_root),
        },
        "slots": {"Q": Q_SLOT, "P": P_SLOT, "A": A_SLOT, "C": C_SLOT},
        "proposers": {
            "epoch 10 (P)": sorted(proposers_of(p_post, E)),
            "epoch 11 (A)": sorted(proposers_of(a_post, E + 1)),
            "epoch 12 (C)": sorted(proposers_of(c_post, E + 2)),
            "epoch 12 (P)": sorted(proposers_of(p_post, E + 2)),
        },
        "states": {
            name: {
                "justified": state_json(post)["current_justified_checkpoint"],
                "finalized": state_json(post)["finalized_checkpoint"],
            }
            for name, post in (("P", p_post), ("A", a_post), ("C", c_post))
        },
    }
    if v is None:
        return result
    assert v not in voters and v != slashed

    for slot, block in ((Q_SLOT, q_block), (P_SLOT, p_block)):
        tick(slot)
        steps.append(("block", block))
    tick(E * SPE)
    mark("epoch 10 start")
    tick(A_SLOT)
    steps.append(("block", a_block))
    tick((E + 1) * SPE)
    mark("epoch 11 start (A's pull-up promoted)")

    def honest_vote(epoch: int, chain_post: bytes, label: str) -> tuple[dict, int, int]:
        """Tick to v's duty slot, read the store, and build v's vote from the store."""
        slot, index = committee_of(advance(chain_post, epoch * SPE), epoch, v)
        # One second into the slot is before the attestation deadline and in the same slot.
        tick(slot, 1)
        mark(label)
        api = consensus.api_attestation_data(
            PRESET, cx.FORK, g, gb, steps, slot, index, verify=True
        )
        return api["data"], slot, index

    # Vote a: epoch-11 duty, assignment and head on A's chain.
    a_api, s_a, i_a = honest_vote(E + 1, a_post, "vote a (epoch 11 duty)")
    st_a = advance(a_post, s_a)
    a_att = aggregate(st_a, attestation_data(st_a, a_root, A_SLOT, i_a), [v])
    tick(s_a + 1)
    steps.append(("attestation", a_att))
    # C arrives after the duty; its slashing is a carried operation of the block.
    steps.append(("block", c_block))
    mark("epoch 11 after C")

    # Vote b: epoch-12 duty. The head is the fallback, the justified root P, so the assignment
    # comes from P's chain.
    tick((E + 2) * SPE)
    mark("epoch 12 start")
    b_api, s_b, i_b = honest_vote(E + 2, p_post, "vote b (epoch 12 duty)")
    st_b = advance(p_post, s_b)
    b_att = aggregate(st_b, attestation_data(st_b, p_root, P_SLOT, i_b), [v])
    tick(s_b + 1)
    steps.append(("attestation", b_att))
    tick((E + 3) * SPE)
    mark("epoch 13 start")

    groups = consensus.fork_choice(PRESET, cx.FORK, g, gb, steps, True, cx.OVERRIDES)
    outcomes = cx.handler_outcomes(steps, groups)
    carried = {k: len(group) - 1 for k, group in enumerate(groups) if steps[k][0] == "block"}

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
            # With an empty filtered tree the read lists the justified root alone.
            "viable_leaves": sorted(
                (hx(e["root"]), e["weight"]) for e in o["viable_for_head_roots_and_weights"]
            ),
        }

    # Recompute each vote by hand from the head the store returned.
    posts = {
        hx(a_root): (a_post, A_SLOT),
        hx(p_root): (p_post, P_SLOT),
        hx(c_root): (c_post, C_SLOT),
    }

    def by_hand(name: str, slot: int, index: int) -> dict:
        head = read(name)["head"]
        post, head_slot = posts[head["root"]]
        assert head_slot == head["slot"]
        st = advance(post, slot)
        return data_json(attestation_data(st, unhx(head["root"]), head_slot, index))

    assert by_hand("vote a (epoch 11 duty)", s_a, i_a) == a_api
    assert by_hand("vote b (epoch 12 duty)", s_b, i_b) == b_api

    def effective(state: bytes) -> list[int]:
        return sorted({int(x["effective_balance"]) for x in state_json(state)["validators"]})

    result.update(
        {
            "duties": {
                "a": {"slot": s_a, "committee_index": i_a},
                "b": {"slot": s_b, "committee_index": i_b},
            },
            "reads": {name: read(name) for name in marks},
            "vote_a": a_api,
            "vote_b": b_api,
            "a_slashable_with_b": is_slashable(a_api, b_api) or is_slashable(b_api, a_api),
            "carried_operations": {steps[k][0] + f" #{k}": n for k, n in carried.items()},
            "effective_balances": {"P": effective(p_post), "C": effective(c_post)},
            "_raw": {
                "genesis": genesis,
                "anchor": g,
                "anchor_signed": anchor["signed"],
                "blocks": {"Q": q_block, "P": p_block, "A": a_block, "C": c_block},
                "posts": {"Q": q_post, "P": p_post, "A": a_post, "C": c_post},
                "parents": {"Q": g, "P": q_post, "A": p_post, "C": a_post},
                "gossip": {"a": a_att, "b": b_att},
            },
        }
    )
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--v", type=int, default=None)
    parser.add_argument("--fork", default="phase0", choices=["phase0", "altair"])
    parser.add_argument("--out", default=None)
    args = parser.parse_args()
    result = build(args.v, args.fork)
    result.pop("_raw", None)
    text = json.dumps(result, indent=1, default=str)
    if args.out:
        open(args.out, "w").write(text)
    print(text)


if __name__ == "__main__":
    sys.exit(main())
