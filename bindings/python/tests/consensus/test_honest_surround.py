"""An honest validator's two votes, built from its own store, form a surround pair.

The replay in surround_replay.py runs EthLib's genesis, state transition and fork choice handlers,
with every BLS check on, from a genesis anchor (phase0) or a post-upgrade anchor (Altair).
The vote of each duty follows the honest-validator guide: getHead, the head state advanced to the
duty slot, then get_attestation_data. No slashing-protection database is consulted.

The mechanism: the first branch's epoch-r target votes miss the quorum at the first boundary,
65/100 of the stake in validator units, 66/100 here, then meet it at the second empty boundary
because three exits shrink the active set to 97. Only the honest lookahead state sees that
second boundary; the store keeps the one-step pulled-up source, so a competing branch with the
older source stays viable.
"""

import pytest

from . import surround_accountability, surround_replay

FORKS = ("phase0", "altair")
R = surround_replay.R


def epochs(data: dict) -> tuple[int, int]:
    return int(data["source"]["epoch"]), int(data["target"]["epoch"])


@pytest.fixture(scope="module", params=FORKS)
def run(request) -> dict:
    return surround_replay.build(0, False, request.param)


def test_votes_surround(run):
    # Every handler step succeeded inside build, and each vote equals the by-hand chain.
    a, b = run["vote_a"], run["vote_b"]
    assert epochs(a) == (R, R + 2)
    assert epochs(b) == (R - 1, R + 3)
    assert run["a_slashable_with_b"]
    reads = run["reads"]
    roots = run["roots"]
    assert reads["vote a (epoch r+2 duty)"]["head"]["root"] == roots["B"]
    assert reads["vote b (epoch r+3 duty)"]["head"]["root"] == roots["C"]
    for read in reads.values():
        # The store never learns the second-boundary source.
        assert (read["justified"]["epoch"], read["finalized"]["epoch"]) == (R - 1, R - 2)
        assert read["proposer_boost_root"] == "0x" + "00" * 32
    # The honest validator proposes nothing on its head chain in the epochs of the trace.
    for epoch in ("epoch r+1 (B)", "epoch r+2 (B)", "epoch r+3 (C)"):
        assert run["v"] not in run["proposers"][epoch]


@pytest.mark.parametrize("fork", FORKS)
def test_descendant_closes_the_gap(fork):
    # A B descendant whose state crosses into r+1 pulls up source r, and C stops being viable.
    control = surround_replay.build(0, True, fork)
    assert epochs(control["vote_b"]) == (R, R + 3)
    assert not control["a_slashable_with_b"]
    read = control["reads"]["vote b (epoch r+3 duty)"]
    assert read["justified"]["epoch"] == R
    assert [leaf for leaf, _ in read["viable_leaves"]] == [control["roots"]["D"]]


def test_accountability_alternative_fails(run):
    report = surround_accountability.evaluate(run)
    assert report["accountable_keys_on_canonical_runs"] == []
    assert list(report["keys_with_a_slashable_pair_among_all_messages"]) == [str(run["v"])]
    assert report["derived_drift_gwei"] == {"to B": 0, "to C": 0}
    assert not report["A_stake_inequality_holds"]
    assert not report["HashEvidence_holds"]
