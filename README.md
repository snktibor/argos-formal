# fabric-vdr-formal

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23867636.svg)](https://doi.org/10.5281/zenodo.23867636)

A Lean 4 model of guarded revocation on a Hyperledger Fabric verifiable data registry (VDR), with machine-checked proofs.

A guarded revocation is one transaction that revokes a credential only if a list of other revocation registries, the guards, still have the versions the caller saw when it checked them. If two parties guard each other's registries, at most one of their revocations commits. A query followed by an unconditional revocation leaves a time-of-check-to-time-of-use (TOCTOU) window between the two steps, and the guarded revocation closes it.

The model and the proofs belong to the TDK paper *Decentralized verifiable credential revocation with atomic test-and-set for cross-organizational settings* (Tibor Sinka, Budapest University of Technology and Economics, 2026). The chaincode operation that implements guarded revocation, `updateRevRegEntryIfGuardsUnchanged`, is in [fabric-vdr-core](https://github.com/snktibor/fabric-vdr-core).

## Reproduce

With only Docker installed:

```bash
docker run --rm --user "$(id -u):$(id -g)" ghcr.io/snktibor/fabric-vdr-reproduce:v1.0.1 formal
```

The image comes from [`fabric-vdr-core`](https://github.com/snktibor/fabric-vdr-core), the chaincode repository of the same paper. It holds this repository at commit `ae57a65`, the one the paper cites, and runs `lake build --wfail` and `./mutations/check.sh`. To run them from a clone, see [Building](#building).

## Results map

One row per figure and table of the paper that this repository reproduces, all of them in the appendix. [Theorems and where the paper uses them](#theorems-and-where-the-paper-uses-them) maps each theorem to its section. All three rows together take under a minute in the image above.

| Paper | Command | Output |
|---|---|---|
| Figure "A machine-checked theorem proves each security goal" | `lake build --wfail` | The console output. `Axioms.lean` fails the build on a `sorry` or an extra axiom. |
| Table "Further named results of the Lean model" | `lake build --wfail` | The same console output. |
| Table "The mutants of the Lean model" | `lake build --wfail`, `./mutations/check.sh` | The console output of `check.sh` for M1 to M8, and the counterexamples M9 and M10 in `Counterexamples.lean`. |

## Reproduction limits

The proofs reproduce exactly. They are deterministic, `lean-toolchain` pins Lean 4.23.0, and they need no seeds, secrets or special hardware. Elan needs network access once, to download the toolchain.

## Results tag

The paper cites commit `ae57a65`. Release `v1.0.0` keeps those Lean files and the mutations unchanged, and adds the packaging and the [Java value and single-record subset](#java-value-and-single-record-subset). Later versions keep the theorems the paper cites.
The Zenodo version of `v1.0.0` is [10.5281/zenodo.23867637](https://doi.org/10.5281/zenodo.23867637).

## Cite

Cite the concept DOI, which resolves to the newest version; the results tag above names the commit the paper cites. [CITATION.cff](CITATION.cff) holds the same metadata.

```bibtex
@software{sinka2026fabricvdrformal,
  author    = {Sinka, Tibor},
  title     = {fabric-vdr-formal: a {Lean}~4 model and machine-checked proofs of guarded revocation on a {Hyperledger} {Fabric} verifiable data registry},
  year      = {2026},
  publisher = {Zenodo},
  version   = {1.0.0},
  doi       = {10.5281/zenodo.23867636},
  url       = {https://doi.org/10.5281/zenodo.23867636}
}
```

## Building

Install [elan](https://github.com/leanprover/elan) and run `lake build` in the repository root. Elan installs Lean 4.23.0, the version in `lean-toolchain`. The project uses only the Lean core library, without Mathlib.

`lake build` checks every proof. `Axioms.lean` and `JavaValuesAxioms.lean` state the axioms of each main theorem with `#guard_msgs`, so the build fails if a theorem comes to depend on `sorryAx`, on `Lean.ofReduceBool`, which `native_decide` adds, or on any custom axiom. With Lean 4.23.0, every main theorem uses only `propext` and `Quot.sound`. `rejected_detectable`, `rejected_has_prior_committed_writer` and `normal_update_version_bounds` also use `Classical.choice`.

`./mutations/check.sh` applies eight mutations to `ArgosGuard.lean` one at a time and checks that each mutated model fails to build. Each mutation removes one part of the design or one hypothesis, for example the guard on one side or the MVCC read check.

The GitHub workflow runs `lake build --wfail`, which also fails on warnings such as `declaration uses 'sorry'`, and then `./mutations/check.sh`.

## Files

The `Argos` prefix of the Lean files and the namespace is the project's working name.

| File | Contents |
|---|---|
| `ArgosGuard.lean` | The version model of Fabric's validation, `at_most_one`, `rejected_detectable`, and the unguarded race `b1u_both_commit` |
| `ArgosGuardExt.lean` | A model of the endorsement step (`GuardedCall`, `endorse`), the one-sided guard theorem and the stronger detectability theorem |
| `ArgosToctou.lean` | Time and revocation status, `tas_spec`, `window_closed`, `check_holds_at_use`, `no_bifurcation` and `toctou_attack_unguarded` |
| `Counterexamples.lean` | Counterexamples for the mutations, and witnesses that the bounds are sharp and the hypotheses can hold |
| `Axioms.lean` | The axiom check |
| `JavaValues.lean`, `JavaValuesProofs.lean` | Nullable UTF-16 value encoding and 18 representation lemmas |
| `JavaRecordUpdate.lean` | Conditional single-record refinement to `Argos.apply` |
| `JavaValuesAxioms.lean` | Axiom checks for the value/update subset |
| `mutations/` | The eight mutations of `ArgosGuard.lean` as patches, and `check.sh` |

## Java value and single-record subset

[The subset proof](docs/java-correspondence-subset.md) connects a record update satisfying an explicit value-level contract to the existing `Argos.apply` transition for a singleton write set. It also preserves the complete encoded record image. It does **not** prove that Java execution satisfies that contract or establish correspondence for the guarded caller. The original protocol model and proofs are unchanged.

## The model

The state gives each registry key one natural-number version. A transaction has a read set of (key, version) pairs, recorded at endorsement, and a write set of keys. Validation runs over one ordered stream of transactions, one transaction at a time, also inside a block. A transaction commits if every key it read still has the version it saw, and then the version of every key it writes goes up by one. Otherwise the state does not change.

A party's check is a query against a committed prefix of the stream. The use is the validation of its revocation at its position in the stream, after that prefix. No theorem fixes the order of the stream, so the theorems also hold when an attacker chooses the order.

| Lean | Fabric |
|---|---|
| `State`, one version per key | The key's version in the world state, and the entry's `version` field, which every committed write increments |
| `Tx.reads`, `Tx.writes` | The read set and the write set produced at endorsement |
| `committed`, `final` | MVCC validation at commit, in order inside a block (`validateKVRead` in Fabric's `validator.go`) |
| `endorse` returns `none` | The chaincode rejects the call with `FAILED_PRECONDITION` |
| A committed prefix `chk` of the stream | The peer state a client queried during its check |
| `rev`, `RevWF`, `revokedAt` | The credentials a transaction revokes, the rule that a revocation writes its registry, and the revocation status after a prefix |

The model leaves out values, cryptography, key deletion, range queries, endorsement policies, the limit of 16 guards, and validation failures other than MVCC conflicts. It assumes that every peer sees a prefix of the same total order, so forks and an orderer that drops transactions are outside it. A transaction may occur more than once in a stream, which Fabric does not allow, so the modelled attacker is stronger than a real one.

The proofs say nothing about whether the Java chaincode reads and writes what `endorse` describes. Section 4.7 of the paper checks that against the code and the tests.

## Theorems and where the paper uses them

Section numbers refer to the TDK paper. SP1 to SP4 are the security goals of Section 3.2.

Protocol level, in `ArgosToctou.lean`:

| Theorem | Statement | Paper |
|---|---|---|
| `tas_spec` | The transaction of an endorsed guarded call commits in a state if and only if every guard is at its pinned version and the target has the version it had at endorsement. | SP1, Theorem in 3.6 |
| `window_closed` | If every guard is pinned at the version seen at the check and the transaction commits, no transaction that committed between the check and the use wrote a guarded registry. | SP2, Theorem in 3.6 |
| `check_holds_at_use` | A credential the party checked as unrevoked in a guarded registry is still unrevoked when its own revocation commits. | SP2, Theorem in 3.6 |
| `no_bifurcation` | Two parties that follow the guarded protocol for each other's credentials do not both commit, at any positions and with any transactions in between. | SP3, main theorem of 3.6, 4.6 |
| `toctou_attack_unguarded` | On the unguarded path, both revocations commit from the same checked state, both credentials end up revoked, and the second party's check is already false when it commits. | 3.6, scenario B1u in 4.6 |

Version level, in `ArgosGuard.lean` and `ArgosGuardExt.lean`:

| Theorem | Statement | Paper |
|---|---|---|
| `at_most_one` | Two mutually guarded transactions whose pins are not newer than the start state do not both commit, in any stream. | SP3, freshness condition in 3.5, table in 3.6 |
| `at_most_one_endorsed` | The same for two endorsed calls, if the states of the endorsing peers are not newer than the start state. | SP3, 3.5 |
| `mutuallyGuarded_of_endorse` | Two endorsed calls with distinct ids that pin each other's target produce a mutually guarded pair, on any peers and in any states. | 3.5, table in 3.6 |
| `guard_excludes_prior_writer` | If a transaction that guards registry `a`, with a pin not newer than the start state, commits at its position, no transaction that committed before it wrote `a`. Only one side needs to guard. | SP2, table in 3.6 |
| `at_most_one_via_one_sided` | `at_most_one` derived from the one-sided theorem. | Table in 3.6 |
| `stale_never_commits` | Once a key's version passes the version a transaction read, that transaction never commits. | Table and proof outline in 3.6 |
| `final_mono` | Versions never decrease along a stream. | Table and proof outline in 3.6 |
| `at_most_one_from_checked_state` | `at_most_one` for a stream that starts from the state both parties checked. | Not cited in the paper |

Detectability:

| Theorem | Statement | Paper |
|---|---|---|
| `rejected_detectable` | If a transaction with read versions not newer than the start state is in the stream and does not commit, some key it read has a higher version at the end. | SP4, 3.6 |
| `rejected_has_prior_committed_writer` | If a transaction endorsed against the start state does not commit, a transaction that committed before it wrote a key it read. | SP4, Theorem in 3.6 |

Unguarded race, the model's counterpart of scenario B1u:

| Theorem | Statement | Paper |
|---|---|---|
| `b1u_both_commit` | Two unguarded revocations on distinct registries, each reading only its own registry, both commit. | Table in 3.6, 4.6 |
| `b1u_endorsed` | The same race, produced by the endorsement model. | Table in 3.6, 4.6 |

Sharpness and mutations, in `Counterexamples.lean` and `ArgosGuardExt.lean`:

| Theorem | Statement | Paper |
|---|---|---|
| `pair_alone_exactly_one` | If the mutually guarded pair is the whole stream and the first was endorsed against the start state, the first commits and the second is rejected. | 3.7 |
| `ce_neither_commits` | An independent write to both registries ahead of the pair makes both revocations fail, so "exactly one" does not hold in general. | 3.7 |
| `ce_order_decides_1` to `_3` | With an independent write to one registry, the positions decide which revocation, if any, commits. | 3.7 |
| `ToctouExample.stepA`, `stepB` | A concrete pair of steps that satisfies every hypothesis of `no_bifurcation`. | 3.7 |
| `ce_M1`, `ce_M3` to `ce_M8` | For each mutation of the model, a stream in which both revocations commit, so the statement itself becomes false. M2 is M1 with the roles swapped and has no separate counterexample. | 3.7, Appendix A |
| `ce_M6` | A guard pinned at a version newer than the state lets both revocations commit, so the freshness hypothesis of `at_most_one` is needed. | 3.5, 3.7 |
| `ce_M9`, `ce_M10` | Both revocations commit if one party does not guard the other's registry, which is M9, or pins a version it read after its check, which is M10. | 3.7 |

`committed_append`, `final_append`, `version_grows_has_writer` and `writer_bumps` in `ArgosGuardExt.lean` are lemmas for the proofs above.

## License

Copyright 2026 Tibor Sinka. Licensed under the Apache License 2.0, see `LICENSE`.
