"""Evaluate the accountability alternative A of the honest-vote statement on the replayed execution.

A (artifact a038cf6c rev 7, "Shared notation") asks, for runs `left`, `right` from the anchor to
two states held by the honest validator, for

  stake(unslashed at anchor) <= 3 * stake(accountableKeys pre left right)
                                + 2 * max(derivedDrift J left, derivedDrift J right)
  or HashEvidence(objects of pre.left ++ pre.right).

Here the anchor is the genesis state, so pre is the empty run. This script evaluates each term on
the canonical runs (the blocks the store imported, with empty slots between them), following the
Lean definitions:

- Accountable (DirectSafety/Conflict.lean): two block-applied votes of a key that
  is_slashable_attestation_data punishes, or slashing evidence in a block of a tail.
- stateDrift / derivedDrift (DirectSafety/Drift.lean): 2*referenceLoss + referenceGain
  + 2*boundaryStake, maximised over the states of the run up to epoch high + 1.
- HashEvidence (DirectSafety/Hashes.lean): a SHA-256 collision among the node-hash inputs of the
  run's block headers, or a header or state whose root is zero.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import sys

from . import surround_builders as cx, surround_replay as replay
from .surround_builders import (
    PRESET,
    SPE,
    ZERO32,
    advance,
    committees,
    consensus,
    hx,
    is_slashable,
    root,
    state_json,
    state_slot,
    to_json,
    to_ssz,
    unhx,
)


def bits(hexbits: str) -> list[bool]:
    raw = unhx(hexbits)
    flat = [(byte >> k) & 1 == 1 for byte in raw for k in range(8)]
    length = max(i for i, b in enumerate(flat) if b)  # the delimiter bit
    return flat[:length]


def voters(pre: bytes, attestation: dict) -> list[int]:
    data = attestation["data"]
    for com in committees(pre, int(data["target"]["epoch"])):
        if com["slot"] == data["slot"] and com["index"] == data["index"]:
            members = [int(x) for x in com["validators"]]
            flags = bits(attestation["aggregation_bits"])
            assert len(flags) == len(members)
            return [m for m, f in zip(members, flags, strict=True) if f]
    raise LookupError(data)


def block_votes(parent_post: bytes, signed: bytes) -> tuple[list[tuple[int, dict]], dict]:
    block = to_json("SignedBeaconBlock", signed)["message"]
    pre = advance(parent_post, int(block["slot"]))
    out = []
    for att in block["body"]["attestations"]:
        out += [(v, att["data"]) for v in voters(pre, att)]
    return out, block


def gossip_votes(chain_post: bytes, attestation: bytes) -> list[tuple[int, dict]]:
    att = to_json("Attestation", attestation)
    pre = advance(chain_post, int(att["data"]["slot"]))
    return [(v, att["data"]) for v in voters(pre, att)]


def slashable_keys(votes: list[tuple[int, dict]]) -> dict[int, list]:
    by_key: dict[int, list[dict]] = {}
    for v, d in votes:
        if d not in by_key.setdefault(v, []):
            by_key[v].append(d)
    found = {}
    for v, ds in by_key.items():
        pairs = [(a, b) for a, b in itertools.permutations(ds, 2) if is_slashable(a, b)]
        if pairs:
            found[v] = pairs
    return found


# --- drift ------------------------------------------------------------------------------------


def registry(state: bytes) -> dict:
    sj = state_json(state)
    epoch = int(sj["slot"]) // SPE
    previous = max(epoch - 1, 0)
    vals = sj["validators"]

    def active(v, e):
        return int(v["activation_epoch"]) <= e < int(v["exit_epoch"])

    eff = {v["pubkey"]: int(v["effective_balance"]) for v in vals}
    slashed = {v["pubkey"] for v in vals if v["slashed"]}
    act = {v["pubkey"] for v in vals if active(v, epoch)}
    prev = {v["pubkey"] for v in vals if active(v, previous)}
    return {
        "epoch": epoch,
        "eff": eff,
        "active": act,
        "unslashed": act - slashed,
        "recent": (act | prev) - slashed,
        "slashed": slashed,
    }


def state_drift(x: dict, y: dict) -> int:
    def supported(keys, weights, k):
        return weights.get(k, 0) if k in keys else 0

    loss = sum(
        max(x["eff"][k] - supported(y["recent"], y["eff"], k), 0)
        for k in x["unslashed"]
        if k not in y["slashed"]
    )
    gain = sum(max(y["eff"][k] - supported(x["unslashed"], x["eff"], k), 0) for k in y["recent"])
    boundary = sum(y["eff"][k] for k in y["recent"] - y["active"])
    return 2 * loss + gain + 2 * boundary


# --- hash evidence ----------------------------------------------------------------------------


def header_messages(header: dict) -> tuple[bytes, list[bytes]]:
    """The 64-byte node-hash inputs of a BeaconBlockHeader's SSZ Merkle tree, and its root."""
    leaves = [
        int(header["slot"]).to_bytes(32, "little"),
        int(header["proposer_index"]).to_bytes(32, "little"),
        unhx(header["parent_root"]),
        unhx(header["state_root"]),
        unhx(header["body_root"]),
        ZERO32,
        ZERO32,
        ZERO32,
    ]
    messages = []
    level = leaves
    while len(level) > 1:
        nxt = []
        for a, b in zip(level[::2], level[1::2], strict=True):
            messages.append(a + b)
            nxt.append(hashlib.sha256(a + b).digest())
        level = nxt
    top = level[0]
    assert top == root("BeaconBlockHeader", to_ssz("BeaconBlockHeader", header))
    return top, messages


def cached_state(state: bytes, fork: str | None = None) -> bytes:
    """process_slot's cache step: state root, filled header state root, block root."""
    fork = fork or cx.FORK
    sj = consensus.api_json(PRESET, fork, "BeaconState", state)
    slot = int(sj["slot"])
    state_root = consensus.ssz_static(PRESET, fork, "BeaconState", state)[0]
    sj["state_roots"][slot % 64] = hx(state_root)
    if unhx(sj["latest_block_header"]["state_root"]) == ZERO32:
        sj["latest_block_header"]["state_root"] = hx(state_root)
    header_root = root("BeaconBlockHeader", to_ssz("BeaconBlockHeader", sj["latest_block_header"]))
    sj["block_roots"][slot % 64] = hx(header_root)
    return consensus.api_ssz(PRESET, fork, "BeaconState", sj)


def pre_objects(genesis: bytes, anchor_signed: bytes, anchor: bytes) -> tuple[list, list]:
    """(state roots, headers) of the run from the phase0 genesis to the Altair anchor."""
    roots, headers = [], []
    current, fork = genesis, "phase0"
    block = to_json("SignedBeaconBlock", anchor_signed)["message"]
    while True:
        sj = consensus.api_json(PRESET, fork, "BeaconState", current)
        roots.append(consensus.ssz_static(PRESET, fork, "BeaconState", current)[0])
        headers.append(sj["latest_block_header"])
        if int(sj["slot"]) == int(block["slot"]):
            break
        cached = cached_state(current, fork)
        roots.append(consensus.ssz_static(PRESET, fork, "BeaconState", cached)[0])
        headers.append(
            consensus.api_json(PRESET, fork, "BeaconState", cached)["latest_block_header"]
        )
        current = consensus.process_slots(PRESET, fork, current, 1, cx.OVERRIDES)
        if fork == "phase0" and int(sj["slot"]) + 1 == SPE:
            current = consensus.upgrade_state(PRESET, cx.FORK, current, True, cx.OVERRIDES)
            fork = cx.FORK
    headers.append(
        {
            "slot": block["slot"],
            "proposer_index": block["proposer_index"],
            "parent_root": block["parent_root"],
            "state_root": block["state_root"],
            "body_root": hx(root("BeaconBlockBody", to_ssz("BeaconBlockBody", block["body"]))),
        }
    )
    roots.append(root("BeaconState", anchor))
    headers.append(state_json(anchor)["latest_block_header"])
    return roots, headers


def run_objects(genesis: bytes, chain: list[tuple[bytes, bytes]]) -> tuple[list, list, list]:
    """States, headers and per-state registries of the canonical run from genesis through
    each (signed block, post-state) in order, one slot step at a time."""
    states, headers, regs = [genesis], [], [registry(genesis)]
    current = genesis
    for signed, post in chain:
        block = to_json("SignedBeaconBlock", signed)["message"]
        while state_slot(current) < int(block["slot"]):
            cached = cached_state(current)
            nxt = consensus.process_slots(PRESET, cx.FORK, current, 1, cx.OVERRIDES)
            # The cache step must agree with the transition's own next slot.
            nj, cj = state_json(nxt), state_json(cached)
            assert nj["block_roots"] == cj["block_roots"] and nj["state_roots"] == cj["state_roots"]
            states += [cached, nxt]
            regs.append(registry(nxt))
            current = nxt
        headers.append(
            {
                "slot": block["slot"],
                "proposer_index": block["proposer_index"],
                "parent_root": block["parent_root"],
                "state_root": block["state_root"],
                "body_root": hx(root("BeaconBlockBody", to_ssz("BeaconBlockBody", block["body"]))),
            }
        )
        states.append(post)
        regs.append(registry(post))
        current = post
    for s in states:
        headers.append(state_json(s)["latest_block_header"])
    return states, headers, regs


def evaluate(result: dict) -> dict:
    """Each term of A on the canonical runs of a replay built by surround_replay.build."""
    fork = result["fork"]
    raw = result["_raw"]
    g, posts, blocks, gossip = raw["anchor"], raw["posts"], raw["blocks"], raw["gossip"]
    v = result["v"]
    parents = {"X": g, "Q": posts["X"], "P": posts["Q"], "C": posts["P"], "B": posts["P"]}

    # Block-applied votes and slashings, per block.
    applied: dict[str, list] = {}
    slashings = {}
    for name in ("X", "Q", "P", "C", "B"):
        votes, block = block_votes(parents[name], blocks[name])
        applied[name] = votes
        body = block["body"]
        slashings[name] = len(body["proposer_slashings"]) + len(body["attester_slashings"])
    run_votes = {
        "to B": applied["X"] + applied["Q"] + applied["P"] + applied["B"],
        "to C": applied["X"] + applied["Q"] + applied["P"] + applied["C"],
    }
    accountable_runs = slashable_keys(run_votes["to B"] + run_votes["to C"])

    # Every vote message of the execution, including gossip and v's two votes.
    every = run_votes["to B"] + applied["C"]
    every += gossip_votes(posts["B"], gossip["w1"])
    every += [x for c in gossip["c_votes"] for x in gossip_votes(posts["C"], c)]
    every += gossip_votes(posts["B"], gossip["a"]) + gossip_votes(posts["C"], gossip["b"])
    accountable_all = slashable_keys(every)

    # Drift and hash evidence along both canonical runs.
    x = registry(g)
    reference = sum(x["eff"][k] for k in x["unslashed"])
    high = result["reads"]["vote b (epoch r+3 duty)"]["justified"]["epoch"]
    drift, zero_roots, collisions, counts = {}, [], [], {}
    all_messages: dict[bytes, bytes] = {}
    pre_roots, pre_headers = ([], [])
    if raw["anchor_signed"] is not None:
        pre_roots, pre_headers = pre_objects(raw["genesis"], raw["anchor_signed"], g)
        zero_roots += [("pre state", "pre") for r in pre_roots if r == ZERO32]
        counts["pre"] = {"states": len(pre_roots), "headers": len(pre_headers)}
    for label, chain in (("to B", ["X", "Q", "P", "B"]), ("to C", ["X", "Q", "P", "C"])):
        states, headers, regs = run_objects(g, [(blocks[n], posts[n]) for n in chain])
        drift[label] = max(state_drift(x, y) for y in regs if y["epoch"] <= high + 1)
        assert max(y["epoch"] for y in regs) <= high + 1
        counts[label] = {"states": len(states), "headers": len(headers)}
        for s in states:
            if root("BeaconState", s) == ZERO32:
                zero_roots.append(("state", label))
        for h in headers + pre_headers:
            top, messages = header_messages(h)
            if top == ZERO32:
                zero_roots.append(("header", label))
            for m in messages:
                digest = hashlib.sha256(m).digest()
                if all_messages.setdefault(digest, m) != m:
                    collisions.append((hx(digest), hx(m), hx(all_messages[digest])))

    # Not part of A: the drift the virtual lookahead states would show if they were charged.
    s_a = result["duties"]["a"]["slot"]
    s_b = result["duties"]["b"]["slot"]
    after = replay.R + 1
    virtual = [advance(posts["B"], t) for t in range(after * SPE, s_a + 1, SPE)]
    virtual += [advance(posts["C"], t) for t in range(after * SPE, s_b + 1, SPE)]
    virtual_drift = max(state_drift(x, registry(y)) for y in virtual)

    # Accountable stake: effective balances at the anchor of the accountable unslashed keys.
    anchor_keys = [val["pubkey"] for val in state_json(g)["validators"]]
    acc_stake = sum(
        x["eff"][anchor_keys[k]] for k in accountable_runs if anchor_keys[k] in x["unslashed"]
    )
    rhs = 3 * acc_stake + 2 * max(drift.values())
    report = {
        "fork": fork,
        "v": v,
        "slashings_in_blocks": slashings,
        "block_applied_votes": {k: len(vs) for k, vs in applied.items()},
        "accountable_keys_on_canonical_runs": sorted(accountable_runs),
        "keys_with_a_slashable_pair_among_all_messages": {
            str(k): [
                [
                    p[0]["source"]["epoch"] + "->" + p[0]["target"]["epoch"],
                    p[1]["source"]["epoch"] + "->" + p[1]["target"]["epoch"],
                ]
                for p in ps
            ]
            for k, ps in accountable_all.items()
        },
        "reference_stake_gwei": reference,
        "derived_drift_gwei": drift,
        "high (store J epoch at vote b)": high,
        "drift_if_virtual_lookahead_states_were_charged_gwei": virtual_drift,
        "A_stake_inequality": f"{reference} <= 3*{acc_stake} + 2*{max(drift.values())} = {rhs}",
        "A_stake_inequality_holds": reference <= rhs,
        "hash_evidence": {
            "zero_roots": zero_roots,
            "collisions": collisions,
            "distinct_header_messages": len(all_messages),
            "objects": counts,
        },
        "HashEvidence_holds": bool(zero_roots or collisions),
    }
    return report


def main() -> None:
    fork = sys.argv[2] if len(sys.argv) > 2 else "phase0"
    report = evaluate(replay.build(0, False, fork))
    print(json.dumps(report, indent=1))
    if len(sys.argv) > 1:
        open(sys.argv[1], "w").write(json.dumps(report, indent=1))


if __name__ == "__main__":
    main()
