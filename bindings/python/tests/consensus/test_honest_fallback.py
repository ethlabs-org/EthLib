"""A slashing in a block empties the filtered tree, and the honest fallback vote surrounds.

The replay in fallback_replay.py runs EthLib's genesis, state transition and fork choice handlers,
with every BLS check on. The two votes follow the honest-validator guide from the store.
"""

import pytest

from . import fallback_replay, surround_accountability

FORKS = ("phase0", "altair")
E = fallback_replay.E
V = {"phase0": 8, "altair": 7}


def epochs(data: dict) -> tuple[int, int]:
    return int(data["source"]["epoch"]), int(data["target"]["epoch"])


@pytest.fixture(scope="module", params=FORKS)
def run(request) -> dict:
    return fallback_replay.build(V[request.param], request.param)


def test_filter_empties_and_fallback_vote_surrounds(run):
    reads, roots = run["reads"], run["roots"]
    # A's pull-up is recorded and promoted at epoch 11; C's slashing leaves C at source 9.
    assert run["states"]["A"]["justified"]["epoch"] == str(E - 1)
    assert run["states"]["C"]["justified"]["epoch"] == str(E - 1)
    start11 = reads["epoch 11 start (A's pull-up promoted)"]
    assert start11["justified"]["epoch"] == E
    assert start11["head"]["root"] == roots["A"]
    # Within two epochs of its source, C is still viable at epoch 11.
    assert [leaf for leaf, _ in reads["epoch 11 after C"]["viable_leaves"]] == [roots["C"]]
    # From epoch 12 the filtered tree is empty: the read lists the justified root P alone,
    # although P has descendants, and the head is P.
    for name in ("epoch 12 start", "vote b (epoch 12 duty)", "epoch 13 start"):
        read = reads[name]
        assert read["justified"] == {"epoch": E, "root": roots["P"]}
        assert [leaf for leaf, _ in read["viable_leaves"]] == [roots["P"]]
        assert read["head"]["root"] == roots["P"]
    assert reads["vote a (epoch 11 duty)"]["head"]["root"] == roots["A"]
    assert epochs(run["vote_a"]) == (E, E + 1)
    assert epochs(run["vote_b"]) == (E - 1, E + 2)
    assert run["a_slashable_with_b"]
    for epoch in run["proposers"].values():
        assert run["v"] not in epoch


def test_accountability_alternative_fails(run):
    raw = run["_raw"]
    report = surround_accountability.evaluate_runs(
        fork=run["fork"],
        v=run["v"],
        genesis=raw["genesis"],
        anchor=raw["anchor"],
        anchor_signed=raw["anchor_signed"],
        blocks=raw["blocks"],
        posts=raw["posts"],
        parents=raw["parents"],
        chains={"to A": ["Q", "P", "A"], "to C": ["Q", "P", "A", "C"]},
        messages=[(raw["posts"]["A"], raw["gossip"]["a"]), (raw["posts"]["P"], raw["gossip"]["b"])],
        high=run["reads"]["vote b (epoch 12 duty)"]["justified"]["epoch"],
        virtual=[],
    )
    # Only the validator that C slashes is accountable: 32 ETH of the 3200 ETH reference.
    assert report["keys_with_slashable_block_votes"] == []
    assert report["accountable_keys_on_canonical_runs"] == [run["slashed"]]
    assert report["accountable_stake_gwei"] == 32 * 10**9
    assert report["derived_drift_gwei"] == {"to A": 0, "to C": 0}
    assert not report["A_stake_inequality_holds"]
    assert not report["HashEvidence_holds"]
    assert sorted(report["keys_with_a_slashable_pair_among_all_messages"]) == [str(run["v"])]
