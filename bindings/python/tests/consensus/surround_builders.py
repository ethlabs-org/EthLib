"""Helpers for a store-level replay through EthLib's compiled handlers (phase0, minimal preset).

Every state transition, store handler, committee, attestation data and signature check below is
computed by EthLib's own exports. This file only assembles inputs: keys, SSZ documents and
signatures over signing roots that EthLib computes.
"""

from __future__ import annotations

import hashlib
from collections.abc import Sequence
from functools import cache

from py_ecc.bls import G2ProofOfPossession

from ethlib import consensus
from ethlib.cryptography import bls

PRESET = "minimal"
FORK = "phase0"
CONFIG = consensus.config(PRESET)
# Replacements of configuration values, passed to every export that takes them (None: minimal).
OVERRIDES: dict | None = None


def use(fork: str, overrides: dict | None) -> None:
    """Select the fork of the store and the configuration replacements for later calls."""
    global FORK, OVERRIDES
    FORK, OVERRIDES = fork, overrides


P = consensus.preset(PRESET)
SPE = P["SLOTS_PER_EPOCH"]
SLOT_SECONDS = CONFIG["SLOT_DURATION_MS"] // 1000
GWEI = 10**9
FAR_FUTURE = 2**64 - 1

DOMAIN_DEPOSIT = bytes.fromhex("03000000")
DOMAIN_VOLUNTARY_EXIT = bytes.fromhex("04000000")
ZERO32 = bytes(32)
INFINITY_SIG = b"\xc0" + bytes(95)


def hx(b: bytes) -> str:
    return "0x" + b.hex()


def unhx(s: str) -> bytes:
    return bytes.fromhex(s.removeprefix("0x"))


# --- keys -------------------------------------------------------------------------------------


@cache
def secret_key(index: int) -> bytes:
    """A deterministic secret key for validator `index` (32 big-endian bytes)."""
    return bls.key_gen(
        hashlib.sha256(b"honest-vote-counterexample-" + str(index).encode()).digest()
    )


@cache
def public_key(index: int) -> bytes:
    return G2ProofOfPossession.SkToPk(int.from_bytes(secret_key(index), "big"))


# --- SSZ through EthLib -----------------------------------------------------------------------


def to_ssz(type_name: str, doc: object) -> bytes:
    return consensus.api_ssz(PRESET, FORK, type_name, doc)


def to_json(type_name: str, data: bytes) -> dict:
    return consensus.api_json(PRESET, FORK, type_name, data)


def root(type_name: str, data: bytes) -> bytes:
    return consensus.ssz_static(PRESET, FORK, type_name, data)[0]


def signing_root(object_root: bytes, domain: bytes) -> bytes:
    return root("SigningData", object_root + domain)


def compute_domain(domain_type: bytes, version: bytes, genesis_validators_root: bytes) -> bytes:
    fork_data_root = root("ForkData", version + genesis_validators_root)
    return domain_type + fork_data_root[:28]


# --- genesis ----------------------------------------------------------------------------------


def deposits(count: int) -> list[bytes]:
    """Signed deposits of 32 ETH with valid proofs against the incremental deposit tree."""
    version = unhx(CONFIG["GENESIS_FORK_VERSION"])
    domain = compute_domain(DOMAIN_DEPOSIT, version, ZERO32)
    tree = consensus.deposit_tree_new()
    out = []
    for i in range(count):
        pk = public_key(i)
        wc = b"\x00" + hashlib.sha256(pk).digest()[1:]
        amount = P["MAX_EFFECTIVE_BALANCE"]
        message = pk + wc + amount.to_bytes(8, "little")
        sig = bls.sign(secret_key(i), signing_root(root("DepositMessage", message), domain))
        data = {
            "pubkey": hx(pk),
            "withdrawal_credentials": hx(wc),
            "amount": str(amount),
            "signature": hx(sig),
        }
        leaf = root("DepositData", to_ssz("DepositData", data))
        tree = consensus.deposit_tree_push_leaf(tree, leaf)
        got_leaf, proof = consensus.deposit_tree_get_proof(tree, i)
        assert got_leaf == leaf
        out.append(to_ssz("Deposit", {"proof": [hx(x) for x in proof], "data": data}))
    return out


# --- state reads ------------------------------------------------------------------------------


def state_json(state: bytes) -> dict:
    return to_json("BeaconState", state)


def state_slot(state: bytes) -> int:
    return int(state_json(state)["slot"])


def advance(state: bytes, slot: int) -> bytes:
    """EthLib process_slots up to `slot` (no-op when already there)."""
    current = state_slot(state)
    assert slot >= current
    return (
        state
        if slot == current
        else consensus.process_slots(PRESET, FORK, state, slot - current, OVERRIDES)
    )


def proposer(state_at_slot: bytes, count: int) -> int:
    found = [
        i for i in range(count) if consensus.is_proposer(PRESET, FORK, state_at_slot, i, OVERRIDES)
    ]
    assert len(found) == 1, found
    return found[0]


def committees(state: bytes, epoch: int) -> list[dict]:
    """EthLib's Beacon API committees of an epoch: index, slot, validators."""
    return consensus.api_committees(PRESET, FORK, state, epoch=epoch)["data"]


# --- blocks -----------------------------------------------------------------------------------


def block_root(message: bytes) -> bytes:
    return root("BeaconBlock", message)


def genesis_block(genesis: bytes) -> bytes:
    """The phase0 genesis block: the default body, committing to the genesis state."""
    body = {
        "randao_reveal": hx(bytes(96)),
        "eth1_data": {"deposit_root": hx(ZERO32), "deposit_count": "0", "block_hash": hx(ZERO32)},
        "graffiti": hx(ZERO32),
        "proposer_slashings": [],
        "attester_slashings": [],
        "attestations": [],
        "deposits": [],
        "voluntary_exits": [],
    }

    def ssz(type_name, doc):
        return consensus.api_ssz(PRESET, "phase0", type_name, doc)

    def htr(type_name, data):
        return consensus.ssz_static(PRESET, "phase0", type_name, data)[0]

    doc = {
        "slot": "0",
        "proposer_index": "0",
        "parent_root": hx(ZERO32),
        "state_root": hx(htr("BeaconState", genesis)),
        "body": body,
    }
    block = ssz("BeaconBlock", doc)
    header = consensus.api_json(PRESET, "phase0", "BeaconState", genesis)["latest_block_header"]
    assert unhx(header["body_root"]) == htr("BeaconBlockBody", ssz("BeaconBlockBody", body))
    return block


def make_block(
    parent_state: bytes,
    parent_root: bytes,
    slot: int,
    count: int,
    attestations: Sequence[bytes] = (),
    exits: Sequence[dict] = (),
    graffiti: bytes = ZERO32,
) -> tuple[bytes, bytes, bytes]:
    """A fully signed block on a parent; returns (signed block, block root, post-state)."""
    pre = advance(parent_state, slot)
    who = proposer(pre, count)
    eth1 = state_json(pre)["eth1_data"]
    body = {
        "randao_reveal": hx(INFINITY_SIG),
        "eth1_data": eth1,
        "graffiti": hx(graffiti),
        "proposer_slashings": [],
        "attester_slashings": [],
        "attestations": [to_json("Attestation", a) for a in attestations],
        "deposits": [],
        "voluntary_exits": list(exits),
    }
    if FORK != "phase0":
        size = P["SYNC_COMMITTEE_SIZE"]
        body["sync_aggregate"] = {
            "sync_committee_bits": hx(bytes(size // 8)),
            "sync_committee_signature": hx(INFINITY_SIG),
        }
    doc = {
        "slot": str(slot),
        "proposer_index": str(who),
        "parent_root": hx(parent_root),
        "state_root": hx(ZERO32),
        "body": body,
    }
    unsigned = to_ssz("BeaconBlock", doc)
    body["randao_reveal"] = hx(
        consensus.get_validator_signature(
            PRESET, FORK, pre, "randao", unsigned, secret_key(who), OVERRIDES
        )
    )
    unsigned = to_ssz("BeaconBlock", doc)
    doc["state_root"] = hx(
        consensus.compute_new_state_root(
            PRESET, FORK, parent_state, unsigned, verify=False, config=OVERRIDES
        )
    )
    message = to_ssz("BeaconBlock", doc)
    sig = consensus.get_validator_signature(
        PRESET, FORK, pre, "block", message, secret_key(who), OVERRIDES
    )
    signed = to_ssz(
        "SignedBeaconBlock", {"message": to_json("BeaconBlock", message), "signature": hx(sig)}
    )
    post = consensus.state_transition(
        PRESET, FORK, parent_state, signed, verify=True, config=OVERRIDES
    )
    return signed, block_root(message), post


def signed_exit(state: bytes, index: int, epoch: int) -> dict:
    sj = state_json(state)
    gvr = unhx(sj["genesis_validators_root"])
    fork = sj["fork"]
    version = unhx(
        fork["previous_version"] if epoch < int(fork["epoch"]) else fork["current_version"]
    )
    domain = compute_domain(DOMAIN_VOLUNTARY_EXIT, version, gvr)
    message = {"epoch": str(epoch), "validator_index": str(index)}
    obj_root = root("VoluntaryExit", to_ssz("VoluntaryExit", message))
    sig = bls.sign(secret_key(index), signing_root(obj_root, domain))
    return {"message": message, "signature": hx(sig)}


# --- attestations -----------------------------------------------------------------------------


def attestation_data(state_at_slot: bytes, head_root: bytes, head_slot: int, index: int) -> bytes:
    """EthLib's honest-validator get_attestation_data on a state already at the duty slot."""
    return consensus.get_attestation_data(
        PRESET, FORK, state_at_slot, head_root, head_slot, index, 0
    )


def aggregate(state_at_slot: bytes, data: bytes, members: list[int]) -> bytes:
    singles = [
        consensus.construct_attestation(
            PRESET, FORK, state_at_slot, data, v, secret_key(v), OVERRIDES
        )
        for v in members
    ]
    return consensus.construct_aggregate(PRESET, FORK, state_at_slot, data, singles)


def data_json(data: bytes) -> dict:
    return to_json("AttestationData", data)


def is_slashable(a: dict, b: dict) -> bool:
    """consensus-specs is_slashable_attestation_data, on API-JSON attestation data."""
    double = a != b and a["target"]["epoch"] == b["target"]["epoch"]
    sa, ta = int(a["source"]["epoch"]), int(a["target"]["epoch"])
    sb, tb = int(b["source"]["epoch"]), int(b["target"]["epoch"])
    surround = sa < sb and tb < ta
    return double or surround
