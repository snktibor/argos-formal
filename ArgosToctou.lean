/-
  The TOCTOU attack of the self-orchestration protocol, stated and closed
  explicitly. Builds on `ArgosGuard.lean` and `ArgosGuardExt.lean` (both
  imported, unchanged). Lean 4.23.0, core only. Build: `lake build`.

  The protocol step (BPM Forum 2025, ΠVC profile of *Trust No Pool*):
  a party CHECKS that the exclusive alternative's credential is unrevoked in
  the competitor's registry, and later USES that result by revoking its own
  credential. The attack: both parties check the same clean state, both
  revoke, both believe they alone have won (bifurcation).

  What this file adds on top of the version model:
  * Time. All peers see prefixes of one ordered stream `ts` (one total order,
    no forks). A check is a client-side query against a committed prefix
    `chk`; the use is the validation of the party's transaction at its
    position `ts = pre ++ t :: post`, with `chk <+: pre`.
  * Content. `rev t` lists the credentials `(registry, index)` that `t`
    revokes; a revocation writes its registry (`RevWF`), so it bumps that
    registry's version. `revokedAt` is the revocation status after a prefix.

  Contents
  1. `tas_spec`: the guarded call is an atomic test-and-set. Its transaction
     commits iff, at the moment of validation, every guard has its pinned
     version and the target has not moved since endorsement.
  2. `window_closed`: if the pins are the versions seen at the check and the
     transaction commits, no committed transaction wrote a guarded registry
     between the check and the use.
  3. `check_holds_at_use`: so a credential checked unrevoked in a guarded
     registry is still unrevoked when the revocation takes effect.
  4. `no_bifurcation`: two parties following the guarded protocol for each
     other's credentials, at any positions and with any other transactions
     interleaved, do not both commit.
  5. `toctou_attack_unguarded`: the same protocol step on the unguarded path
     is attacked: both commit from the same checked state, both credentials
     end up revoked, and the second party's checked fact is already false
     when it is used.
-/
import ArgosGuard
import ArgosGuardExt
namespace Argos

/-! ## 0. Credentials and revocation status -/

/-- A credential: its revocation registry and its index in that registry. -/
abbrev Cred := Key × Nat

/-- Well-formed revocations: revoking a credential is a write to its registry.
(In the chaincode every committed entry update bumps the registry's `version`.) -/
def RevWF (rev : Tx → List Cred) : Prop :=
  ∀ t x, x ∈ rev t → x.1 ∈ t.writes

/-- Revocation status after the committed prefix `pre`: revoked initially
(`R₀`) or revoked by a transaction that committed in `pre`. -/
def revokedAt (rev : Tx → List Cred) (R₀ : Cred → Prop) (s₀ : State)
    (pre : List Tx) (x : Cred) : Prop :=
  R₀ x ∨ ∃ u ∈ committed s₀ pre, x ∈ rev u

/-- The transaction at the head of `t :: post` commits iff its reads match. -/
theorem mem_committed_head {s : State} {t : Tx} (post : List Tx)
    (h : readsOk s t = true) : t ∈ committed s (t :: post) := by
  simp [committed, h]

/-- A transaction that committed at its position counts for every later prefix. -/
theorem mem_committed_after {s₀ : State} {t : Tx} (pre mid : List Tx)
    (h : readsOk (final s₀ pre) t = true) :
    t ∈ committed s₀ (pre ++ t :: mid) := by
  rw [committed_append]
  exact List.mem_append_right _ (mem_committed_head mid h)

/-! ## 1. Atomic test-and-set -/

/-- The guarded call is a test-and-set: its transaction passes validation in
state `s` iff the test holds in `s` (every guard at its pinned version) and the
target has not moved since endorsement. Test and set happen in one validation
step: there is no state in which the test passed but the set is pending. -/
theorem tas_spec {σe s : State} {c : GuardedCall} {t : Tx}
    (he : endorse σe c = some t) :
    readsOk s t = true ↔ (s c.target = σe c.target ∧ ∀ g ∈ c.guards, s g.1 = g.2) := by
  have hpin := endorse_some_guards_hold he
  have ht := endorse_some_tx he
  constructor
  · intro hok
    have hr := readsOk_spec hok
    rw [ht] at hr
    have htgt : s c.target = σe c.target := by
      simpa using hr _ (List.mem_cons_self ..)
    refine ⟨htgt, fun g hg => ?_⟩
    by_cases hk : g.1 = c.target
    · rw [← hpin g hg, hk, htgt]
    · have hmem : (g.1, σe g.1) ∈ (c.target, σe c.target) ::
          c.otherGuards.map (fun g => (g.1, σe g.1)) := by
        apply List.mem_cons_of_mem
        rw [List.mem_map]
        refine ⟨g, ?_, rfl⟩
        rw [GuardedCall.otherGuards, List.mem_filter]
        exact ⟨hg, by simpa using hk⟩
      have := hr _ hmem
      simp only at this
      rw [this, hpin g hg]
  · intro ⟨htgt, hg⟩
    apply readsOk_of_all
    rw [ht]
    intro r hr
    cases List.mem_cons.mp hr with
    | inl heq => subst heq; exact htgt
    | inr hin =>
      obtain ⟨g, hgm, rfl⟩ := List.mem_map.mp hin
      have hgg : g ∈ c.guards := (List.mem_filter.mp hgm).1
      simp only
      rw [hg g hgg, hpin g hgg]

/-! ## 2. The check-to-use window is closed -/

/-- The verifier queried the committed prefix `chk` and pinned every guard at
the version it saw there. If the transaction commits after the further
transactions `mid`, then no transaction that committed in `mid` wrote any
guarded registry, and every guarded registry is at the version of the check. -/
theorem window_closed {s₀ σe : State} {c : GuardedCall} {t : Tx} (chk mid : List Tx)
    (hpin : ∀ g ∈ c.guards, g.2 = final s₀ chk g.1)
    (he : endorse σe c = some t)
    (huse : readsOk (final s₀ (chk ++ mid)) t = true) :
    ∀ g ∈ c.guards,
      final s₀ (chk ++ mid) g.1 = final s₀ chk g.1 ∧
      ∀ u ∈ committed (final s₀ chk) mid, g.1 ∉ u.writes := by
  intro g hg
  have heq : final s₀ (chk ++ mid) g.1 = final s₀ chk g.1 := by
    rw [((tas_spec he).mp huse).2 g hg, hpin g hg]
  refine ⟨heq, fun u hu hw => ?_⟩
  have hbump := writer_bumps mid (final s₀ chk) u g.1 hu hw
  rw [← final_append, heq] at hbump
  exact Nat.lt_irrefl _ hbump

/-! ## 3. The checked fact still holds at the time of use -/

/-- One party's step of the guarded protocol: it checked `other` unrevoked
against the committed prefix `chk`, pinned every guard at the version seen
there, guards the registry of `other`, its call was endorsed (on any peer, in
any state) into `t`, and `t` revokes `own`. -/
structure GuardedStep (rev : Tx → List Cred) (R₀ : Cred → Prop) (s₀ : State)
    (chk : List Tx) (c : GuardedCall) (t : Tx) (own other : Cred) : Prop where
  checked  : ¬ revokedAt rev R₀ s₀ chk other
  pinned   : ∀ g ∈ c.guards, g.2 = final s₀ chk g.1
  guarded  : ∃ v, (other.1, v) ∈ c.guards
  endorsed : ∃ σe, endorse σe c = some t
  revokes  : own ∈ rev t

/-- If the guarded revocation commits at position `pre` (`chk <+: pre`: the
check was made against a prefix of the stream before it), the credential the
party checked is still unrevoked at that moment. -/
theorem check_holds_at_use {rev : Tx → List Cred} {R₀ : Cred → Prop} {s₀ : State}
    {chk : List Tx} {c : GuardedCall} {t : Tx} {own other : Cred}
    (hwf : RevWF rev) (hs : GuardedStep rev R₀ s₀ chk c t own other)
    {pre : List Tx} (hpre : chk <+: pre)
    (huse : readsOk (final s₀ pre) t = true) :
    ¬ revokedAt rev R₀ s₀ pre other := by
  obtain ⟨mid, rfl⟩ := hpre
  obtain ⟨σe, he⟩ := hs.endorsed
  obtain ⟨v, hv⟩ := hs.guarded
  intro hrev
  rcases hrev with h₀ | ⟨u, hu, hx⟩
  · exact hs.checked (Or.inl h₀)
  · rw [committed_append] at hu
    cases List.mem_append.mp hu with
    | inl hchk => exact hs.checked (Or.inr ⟨u, hchk, hx⟩)
    | inr hmid =>
      exact (window_closed chk mid hs.pinned he huse _ hv).2 u hmid (hwf u other hx)

/-! ## 4. No bifurcation -/

/-- Two parties follow the guarded protocol for each other's credentials:
A checked `xB` unrevoked and revokes `xA`; B checked `xA` unrevoked and revokes
`xB`. Both revocations sit in one ordered stream `ts` at positions after their
own checks; anything else may be interleaved. They do not both commit. -/
theorem no_bifurcation {rev : Tx → List Cred} {R₀ : Cred → Prop} {s₀ : State}
    (hwf : RevWF rev)
    {chkA chkB preA preB postA postB ts : List Tx}
    {cA cB : GuardedCall} {tA tB : Tx} {xA xB : Cred}
    (hA : GuardedStep rev R₀ s₀ chkA cA tA xA xB)
    (hB : GuardedStep rev R₀ s₀ chkB cB tB xB xA)
    (hid : cA.id ≠ cB.id)
    (hposA : ts = preA ++ tA :: postA) (hchkA : chkA <+: preA)
    (hposB : ts = preB ++ tB :: postB) (hchkB : chkB <+: preB) :
    ¬ (readsOk (final s₀ preA) tA = true ∧ readsOk (final s₀ preB) tB = true) := by
  intro ⟨hcA, hcB⟩
  have hne : tA ≠ tB := by
    obtain ⟨σA, heA⟩ := hA.endorsed
    obtain ⟨σB, heB⟩ := hB.endorsed
    intro h
    exact hid (by rw [← endorse_id heA, ← endorse_id heB, h])
  have pA : preA <+: ts := ⟨tA :: postA, hposA.symm⟩
  have pB : preB <+: ts := ⟨tB :: postB, hposB.symm⟩
  rcases List.prefix_or_prefix_of_prefix pA pB with ⟨r, hr⟩ | ⟨r, hr⟩
  · -- A is ordered no later than B
    subst hr
    rw [List.append_assoc] at hposB
    have hcancel := List.append_cancel_left (hposA.symm.trans hposB)
    cases r with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hcancel
      exact hne hcancel.1
    | cons y r =>
      simp only [List.cons_append, List.cons.injEq] at hcancel
      have hy := hcancel.1
      subst hy
      exact check_holds_at_use hwf hB hchkB hcB
        (Or.inr ⟨tA, mem_committed_after preA r hcA, hA.revokes⟩)
  · -- B is ordered before A
    subst hr
    rw [List.append_assoc] at hposA
    have hcancel := List.append_cancel_left (hposB.symm.trans hposA)
    cases r with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hcancel
      exact hne hcancel.1.symm
    | cons y r =>
      simp only [List.cons_append, List.cons.injEq] at hcancel
      have hy := hcancel.1
      subst hy
      exact check_holds_at_use hwf hA hchkA hcA
        (Or.inr ⟨tB, mem_committed_after preB r hcB, hB.revokes⟩)

/-! ## 5. The attack on the unguarded path -/

/-- The unguarded protocol step (`updateRevRegEntry`, the other registry only
queried): both parties check the same state `s₀` (empty prefix), both
revocations commit, both credentials end up revoked, and B's checked fact
(`xA` unrevoked) is already false at B's time of use. -/
theorem toctou_attack_unguarded {rev : Tx → List Cred} {R₀ : Cred → Prop} (s₀ : State)
    (cA cB : GuardedCall) {xA xB : Cred}
    (hab : cA.target ≠ cB.target)
    (hrA : xA ∈ rev (endorseUnguarded s₀ cA)) (hrB : xB ∈ rev (endorseUnguarded s₀ cB)) :
    let tA := endorseUnguarded s₀ cA
    let tB := endorseUnguarded s₀ cB
    readsOk s₀ tA = true ∧ readsOk (final s₀ [tA]) tB = true ∧
    revokedAt rev R₀ s₀ [tA] xA ∧
    revokedAt rev R₀ s₀ [tA, tB] xA ∧ revokedAt rev R₀ s₀ [tA, tB] xB := by
  intro tA tB
  have hc := b1u_endorsed s₀ cA cB hab
  have hba : cB.target ≠ cA.target := fun h => hab h.symm
  have h₁ : readsOk s₀ tA = true := by simp [tA, readsOk, endorseUnguarded]
  have h₂ : readsOk (final s₀ [tA]) tB = true := by
    simp [tA, tB, final, step, readsOk, endorseUnguarded, apply, hba]
  refine ⟨h₁, h₂, Or.inr ⟨tA, by simp [committed, h₁], hrA⟩,
    Or.inr ⟨tA, by rw [hc]; simp [tA], hrA⟩, Or.inr ⟨tB, by rw [hc]; simp [tB], hrB⟩⟩

/-! ## Concrete instance (B1 / B1u fixture), non-vacuity of the hypotheses -/

namespace ToctouExample
open Example

/-- Every write to a registry revokes index 0 of it; A owns `(a, 0)`, B owns `(b, 0)`. -/
def rev (t : Tx) : List Cred := t.writes.map (fun k => (k, 0))

theorem rev_wf : RevWF rev := by
  intro t x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  exact hk

def cA : GuardedCall := ⟨1, a, [(b, 3)]⟩
def cB : GuardedCall := ⟨2, b, [(a, 3)]⟩
def R₀ : Cred → Prop := fun _ => False

/-- Both parties check the empty prefix (state `s₀`); their steps satisfy every
hypothesis of `no_bifurcation`. -/
theorem stepA : GuardedStep rev R₀ s₀ [] cA t₁ (a, 0) (b, 0) where
  checked  := by simp [revokedAt, R₀, committed]
  pinned   := by decide
  guarded  := ⟨3, by decide⟩
  endorsed := ⟨s₀, by decide⟩
  revokes  := by decide

theorem stepB : GuardedStep rev R₀ s₀ [] cB t₂ (b, 0) (a, 0) where
  checked  := by simp [revokedAt, R₀, committed]
  pinned   := by decide
  guarded  := ⟨3, by decide⟩
  endorsed := ⟨s₀, by decide⟩
  revokes  := by decide

-- Guarded: in either order exactly the first one commits, the other is rejected.
example : readsOk s₀ t₁ = true ∧ readsOk (final s₀ [t₁]) t₂ = false := by decide
example : readsOk s₀ t₂ = true ∧ readsOk (final s₀ [t₂]) t₁ = false := by decide
-- Unguarded: both commit and both credentials are revoked (bifurcation).
example : committed s₀ [t₁u, t₂u] = [t₁u, t₂u] := by decide
example : (a, 0) ∈ rev t₁u ∧ (b, 0) ∈ rev t₂u := by decide

end ToctouExample

end Argos
