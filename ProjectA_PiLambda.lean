/-
  Math 7800 (Fall 2026) -- Take-home Lean midterm, Project A.
  Scaffold release: 2026-10-13. Due: Thursday, 2026-10-29, Gradescope.

  Read Midterm/README.md before starting.
  Replace ALL five `sorry` placeholders with proofs (four lemmas and
  the main theorem). None may remain in a final submission.
  Keep the definitions, namespace, and five statements unchanged.
  Add helper lemmas as needed. General Mathlib set algebra is allowed.
  Do not use MeasurableSpace.DynkinSystem.*, any constant beginning
  MeasurableSpace.generateFrom, or MeasurableSpace.induction_on_inter,
  including through a helper lemma. See README.md for the proof map.
  Check the two projects separately: they share the frozen definitions.
-/
import Mathlib
open Set Function

namespace Math7800.Midterm

-- sample space
variable {Ω : Type*}

-- BEGIN FROZEN DEFINITIONS
/-- π-system: closed under finite intersection. (∅ allowed, as in Mathlib.) -/
def IsPiSys (P : Set (Set Ω)) : Prop :=
  ∀ A ∈ P, ∀ B ∈ P, A ∩ B ∈ P
/-
def IsPiSys Define a property called IsPiSys
(P : Set (Set Ω)) P is the a collection of subset of Ω
: Prop the definition produces a mathematical proposition
:= is defined to mean
∀ A ∈ P, ∀ B ∈ P means for every A, B ∈ P
A ∩ B ∈ P means their intersection belong to P
-/

/-- λ-system (Billingsley): contains Ω, closed under complements and
countable disjoint unions. -/
structure IsLambdaSys (L : Set (Set Ω)) : Prop where
  univ_mem : univ ∈ L
  compl_mem : ∀ A ∈ L, Aᶜ ∈ L
  iUnion_mem : ∀ f : ℕ → Set Ω, Pairwise (Disjoint on f) → (∀ n, f n ∈ L) →
    (⋃ n, f n) ∈ L
/-
Structure is used here to package three required properties to satisfies a λ-system
univ ∈ L means the entire underlying space Ω belongs to the collection L
∀ A ∈ L, Aᶜ ∈ L means For every A ∈ L, the complement is also in L
∀ f : ℕ → Set Ω means a function takes a natural number and returns a subset of Ω.
in short, f (n) = A n
Pairwise (Disjoint on f) means that the set sequence are pairwise disjoint
∀ n, f n ∈ L means every set in the sequence belongs to L: A n ∈ L ∀ n ∈ ℕ
(∪ n, f n) ∈ L means the union of the entire sequence also belongs to L: ⋃ A n ∈ L
-/

structure IsSigmaField (F : Set (Set Ω)) : Prop where
  univ_mem : univ ∈ F
  compl_mem : ∀ A ∈ F, Aᶜ ∈ F
  iUnion_mem : ∀ f : ℕ → Set Ω, (∀ n, f n ∈ F) → (⋃ n, f n) ∈ F
/-
the one different from IsLambdaSys and IsSigmaField is
 Pairwise (Disjoint on f) → in IsLambdaSys but not in IsSigmaField.
!Remark : A σ-field is automatically a λ-system, because closure under arbitrary countable unions
!implies closure under countable disjoint unions.
However, a λ-system is not necessarily a σ-field.

structure packages the required proofs together.
F : Set (Set Ω)                means F is a collection of subsets of Ω
: Prop                         means we are describing a proposition.
where                          introduces the required fields.
ℕ → Set Ω                      describes a sequence of sets.
f n                            is the \(n\)-th set.
⋃ n, f n                       is its countable union.
→                              is logical implication.
-/

/-- Field (algebra) of sets. -/
structure IsField (F : Set (Set Ω)) : Prop where
  univ_mem : univ ∈ F
  compl_mem : ∀ A ∈ F, Aᶜ ∈ F
  union_mem : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

/-- Monotone class: closed under increasing unions and decreasing
intersections of sequences. -/
structure IsMonotoneClass (M : Set (Set Ω)) : Prop where
  iUnion_mem : ∀ f : ℕ → Set Ω, Monotone f → (∀ n, f n ∈ M) → (⋃ n, f n) ∈ M
  iInter_mem : ∀ f : ℕ → Set Ω, Antitone f → (∀ n, f n ∈ M) → (⋂ n, f n) ∈ M
--Antitone does not mean that the function is negative. It means order-reversing

def sigmaGen (A : Set (Set Ω)) : Set (Set Ω) := ⋂₀ {F | IsSigmaField F ∧ A ⊆ F}
/-
Lean syntax	                    Mathematical meaning
def sigmaGen	                  Define a generated σ-field
(A : Set (Set Ω))	              A is a collection of subsets of Ω
: Set (Set Ω)	                  The result is another collection of subsets
:=	                            Is defined as
⋂₀	                            Intersection of a collection of sets
{F \| ...}	                    The collection of all F satisfying the condition
IsSigmaField F	                F is a σ-field
∧	                              Logical AND
A ⊆ F	                          Every member of A also belongs to F
-/
def lambdaGen (A : Set (Set Ω)) : Set (Set Ω) := ⋂₀ {L | IsLambdaSys L ∧ A ⊆ L}
def monoGen (A : Set (Set Ω)) : Set (Set Ω) :=
  ⋂₀ {M | IsMonotoneClass M ∧ A ⊆ M}
-- END FROZEN DEFINITIONS

-- ============================================================
-- HELPER 1: Empty Set Membership
-- ============================================================
-- Mathematical statement:
-- If L is a λ-system, then ∅ ∈ L.
--
-- Proof idea:
-- 1. Ω ∈ L by the universal-set property.
-- 2. Ωᶜ ∈ L by complement closure.
-- 3. Since Ωᶜ = ∅, we conclude ∅ ∈ L.

private lemma lambda_empty_mem
    (L : Set (Set Ω))
    -- L is a collection of subsets of Ω.

    (hL : IsLambdaSys L) :
    -- hL establishes that L is a λ-system.
    -- We may use:
    -- hL.univ_mem
    -- hL.compl_mem
    -- hL.iUnion_mem

    (∅ : Set Ω) ∈ L := by
  -- Goal: ∅ ∈ L.

  have h_univ : (univ : Set Ω) ∈ L :=
    hL.univ_mem
  -- have name : proposition := proof
  -- Establish Ω ∈ L using the first λ-system property.
  -- h_univ stores the proof of universal-set membership.

  have h_compl : (univ : Set Ω)ᶜ ∈ L :=
    hL.compl_mem univ h_univ
  -- Apply complement closure to Ω.
  -- h_compl proves Ωᶜ ∈ L.
  -- Since Ωᶜ = ∅, this is equivalent to our goal.

  simpa using h_compl
  -- simp simplifies Ωᶜ to ∅.
  -- The resulting statement matches the goal.


-- ============================================================
-- HELPER 2: Finite Disjoint Union Closure
-- ============================================================
-- Mathematical statement:
-- If A, B ∈ L and A ∩ B = ∅, then A ∪ B ∈ L.
--
-- Proof idea:
-- A λ-system is closed under countable disjoint unions.
-- We construct a sequence:
--
-- f(0) = A
-- f(1) = B
-- f(n) = ∅ for n ≥ 2.
--
-- Then ⋃ n, f n = A ∪ B.
--
-- To apply countable disjoint union closure, prove:
-- 1. Every f n belongs to L.
-- 2. The sequence f is pairwise disjoint.
-- 3. Its union equals A ∪ B.

private lemma lambda_union_mem_of_disjoint
    (L : Set (Set Ω))
    (hL : IsLambdaSys L)
    (A B : Set Ω)
    (hA : A ∈ L)
    (hB : B ∈ L)
    (hAB : Disjoint A B) :
    A ∪ B ∈ L := by

  -- Construct a sequence whose first two terms are A and B.
  let f : ℕ → Set Ω :=
    fun n =>
      if n = 0 then A
      else if n = 1 then B
      else ∅

  -- Thus:
  -- f 0 = A
  -- f 1 = B
  -- f n = ∅ for n ≠ 0, 1.
  --
  -- Mathematically:
  -- ⋃ n, f n = A ∪ B ∪ ∅ ∪ ∅ ∪ ...
  --           = A ∪ B.

  -- ----------------------------------------------------------
  -- GOAL 1: Every term of f belongs to L.
  -- ----------------------------------------------------------

  have hf_mem : ∀ n, f n ∈ L := by
    -- Goal: ∀ n, f n ∈ L.

    intro n
    -- Fix an arbitrary natural number n.
    -- Goal: f n ∈ L.

    by_cases h0 : n = 0
    -- Split into two cases:
    -- pos: n = 0
    -- neg: n ≠ 0.

    case pos =>
      simp [f, h0, hA]
      -- Since n = 0, f n = A.
      -- The goal reduces to A ∈ L.
      -- This is proved using hA.

    case neg =>
      -- We now know n ≠ 0.

      by_cases h1 : n = 1
      -- Split into:
      -- pos: n = 1
      -- neg: n ≠ 1.

      case pos =>
        simp [f, h1, hB]
        -- Since n = 1 and n ≠ 0, f n = B.
        -- hB proves B ∈ L.

      case neg =>
        simp [f, h0, h1, lambda_empty_mem L hL]
        -- Since n ≠ 0 and n ≠ 1, f n = ∅.
        -- Helper 1 proves ∅ ∈ L.
        -- Therefore, f n ∈ L.

  -- We have established:
  -- ∀ n ∈ ℕ, f n ∈ L.


  -- ----------------------------------------------------------
  -- GOAL 2: Prove f is pairwise disjoint.
  -- ----------------------------------------------------------

  have hf_disjoint : Pairwise (Disjoint on f) := by
    -- Mathematical goal:
    -- ∀ i j ∈ ℕ, i ≠ j → Disjoint (f i) (f j).
    --
    -- Equivalently:
    -- For distinct i and j,
    -- f(i) ∩ f(j) = ∅.

    intro i j hij
    -- Introduce arbitrary indices i and j.
    -- hij : i ≠ j.
    -- Goal: Disjoint (f i) (f j).

    change Disjoint (f i) (f j)
    -- Express the pairwise-disjointness goal
    -- explicitly for the two indexed sets.

    have hBA : Disjoint B A := hAB.symm
    -- hAB proves that A and B are disjoint.
    -- Disjointness is symmetric, so B and A
    -- are also disjoint.
    --
    -- We need this because the indices may occur
    -- in either order:
    -- i = 0, j = 1 gives A and B.
    -- i = 1, j = 0 gives B and A.

    by_cases hi0 : i = 0 <;>
      by_cases hi1 : i = 1 <;>
      by_cases hj0 : j = 0 <;>
      by_cases hj1 : j = 1 <;>
      simp_all [f]

    -- by_cases splits according to whether
    -- each index equals 0 or 1.
    --
    -- The operator <;> applies the following
    -- tactic to every generated goal.
    --
    -- simp_all [f] simplifies the definition of f
    -- using all available hypotheses.
    --
    -- The possible nonempty combinations are:
    -- f(0) = A and f(1) = B,
    -- or f(1) = B and f(0) = A.
    --
    -- These are disjoint by hAB and hBA.
    --
    -- If either index is neither 0 nor 1,
    -- its corresponding set is ∅, which is
    -- disjoint from every set.
    --
    -- The cases i = j are impossible because
    -- hij asserts i ≠ j.
    --
    -- Therefore f is pairwise disjoint.


  -- ----------------------------------------------------------
  -- GOAL 3: Prove ⋃ n, f n = A ∪ B.
  -- ----------------------------------------------------------
  -- We establish equality by proving both inclusions.


  -- Direction 1:
  -- (⋃ n, f n) ⊆ A ∪ B.

  have hforward : (⋃ n, f n) ⊆ A ∪ B := by
    -- Goal: Every element of ⋃ n, f n belongs to A ∪ B.

    intro x hx
    -- Choose an arbitrary element x.
    -- hx : x ∈ ⋃ n, f n.
    -- Goal: x ∈ A ∪ B.

    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    -- By the definition of indexed union,
    -- x ∈ ⋃ n, f n means:
    -- There exists n such that x ∈ f n.
    --
    -- We obtain:
    -- n  : ℕ
    -- hn : x ∈ f n.

    change x ∈
      (if n = 0 then A else if n = 1 then B else ∅) at hn
    -- Expand the definition of f n in hypothesis hn.
    -- Now the membership statement explicitly
    -- depends on whether n = 0, n = 1, or neither.

    split_ifs at hn <;> simp_all
    -- split_ifs considers the branches of
    -- the conditional definition of f.
    --
    -- Case 1: n = 0.
    -- Then x ∈ A, so x ∈ A ∪ B.
    --
    -- Case 2: n ≠ 0 and n = 1.
    -- Then x ∈ B, so x ∈ A ∪ B.
    --
    -- Case 3: n ≠ 0 and n ≠ 1.
    -- Then x ∈ ∅, which is impossible.
    --
    -- simp_all completes these cases.

  -- Hence ⋃ n, f n ⊆ A ∪ B.


  -- Direction 2:
  -- A ∪ B ⊆ ⋃ n, f n.

  have hbackward : A ∪ B ⊆ (⋃ n, f n) := by
    -- Goal: Every element of A ∪ B
    -- belongs to the indexed union.

    intro x hx
    -- Fix arbitrary x ∈ A ∪ B.
    -- Goal: x ∈ ⋃ n, f n.

    rcases hx with hx | hx
    -- Membership in A ∪ B means:
    -- x ∈ A or x ∈ B.
    --
    -- Split into two cases.

    case inl =>
      -- Case 1: x ∈ A.
      -- We will show x ∈ f 0.

      exact Set.mem_iUnion.mpr
        ⟨0, by simpa [f] using hx⟩
      -- Set.mem_iUnion.mpr proves membership
      -- in an indexed union using a witness.
      --
      -- We choose n = 0.
      -- Since f 0 = A and x ∈ A,
      -- we obtain x ∈ f 0.
      -- Hence x ∈ ⋃ n, f n.

    case inr =>
      -- Case 2: x ∈ B.
      -- We will show x ∈ f 1.

      exact Set.mem_iUnion.mpr
        ⟨1, by simpa [f] using hx⟩
      -- Choose n = 1.
      -- Since f 1 = B and x ∈ B,
      -- we obtain x ∈ f 1.
      -- Hence x ∈ ⋃ n, f n.

  -- Therefore A ∪ B ⊆ ⋃ n, f n.


  have h_union : (⋃ n, f n) = A ∪ B :=
    Set.Subset.antisymm hforward hbackward
  -- Set equality is proved by mutual inclusion:
  --
  -- hforward  : ⋃ n, f n ⊆ A ∪ B
  -- hbackward : A ∪ B ⊆ ⋃ n, f n
  --
  -- Hence ⋃ n, f n = A ∪ B.


  -- ----------------------------------------------------------
  -- GOAL 4: Apply countable disjoint union closure.
  -- ----------------------------------------------------------

  have h_big_union : (⋃ n, f n) ∈ L :=
    hL.iUnion_mem  f  hf_disjoint  hf_mem
  -- Apply the third λ-system property.
  --
  -- f           : sequence of sets
  -- hf_disjoint : f is pairwise disjoint
  -- hf_mem      : every f n belongs to L
  --
  -- Therefore the countable union belongs to L.

  rw [h_union] at h_big_union
  -- Rewrite the indexed union as A ∪ B.
  -- h_big_union now proves A ∪ B ∈ L.

  exact h_big_union
  -- This matches the original goal.
  -- Helper 2 is proved.


-- ============================================================
-- HELPER 3: Relative Difference Closure
-- ============================================================
-- Mathematical statement:
-- If A, B ∈ L and A ⊆ B,
-- then B \ A ∈ L.
--
-- IMPORTANT:
-- We cannot generally conclude B \ A ∈ L
-- for arbitrary A, B ∈ L without A ⊆ B.
--
-- Proof idea:
-- 1. Since A ⊆ B, A and Bᶜ are disjoint.
-- 2. Since B ∈ L, complement closure gives Bᶜ ∈ L.
-- 3. By Helper 2, A ∪ Bᶜ ∈ L.
-- 4. By complement closure, (A ∪ Bᶜ)ᶜ ∈ L.
-- 5. Since (A ∪ Bᶜ)ᶜ = B \ A,
--    conclude B \ A ∈ L.

private lemma lambda_diff_mem
    (L : Set (Set Ω))
    (hL : IsLambdaSys L)
    (A B : Set Ω)
    (hA : A ∈ L)
    (hB : B ∈ L)
    (hAB : A ⊆ B) :
    B \ A ∈ L := by

  -- Goal: B \ A ∈ L.

  have hdisj : Disjoint A Bᶜ := by
    -- Establish A ∩ Bᶜ = ∅.
    -- This follows because A ⊆ B.

    apply Set.disjoint_left.mpr
    -- changes the disjointness goal into an elementwise implication:
    -- if an element belongs to both sets, derive a contradiction.
    -- Goal: ⊢ ∀ ⦃a : Ω⦄, a ∈ A → a ∉ Bᶜ

    intro x hxA hxBc
    -- x   : Ω
    -- hxA : x ∈ A
    -- hxBc: x ∈ Bᶜ, meaning x ∉ B.
    -- Goal: False.

    exact hxBc (hAB hxA)
    -- notation here mean apply hxBc to (hAB, hxA) produces a contradiction
    -- Since A ⊆ B and x ∈ A,
    -- hAB hxA proves x ∈ B.
    -- But hxBc states x ∉ B.
    -- This contradiction proves disjointness.

  have hunion : A ∪ Bᶜ ∈ L :=
    lambda_union_mem_of_disjoint L hL A Bᶜ
      hA (hL.compl_mem B hB) hdisj
  -- USE HELPER 2.
  --
  -- hA proves A ∈ L.
  -- hL.compl_mem B hB proves Bᶜ ∈ L.
  -- hdisj proves Disjoint A Bᶜ.
  --
  -- Helper 2 gives A ∪ Bᶜ ∈ L.

  have hcompl : (A ∪ Bᶜ)ᶜ ∈ L :=
    hL.compl_mem (A ∪ Bᶜ) hunion
  -- Apply complement closure to A ∪ Bᶜ.
  -- Therefore (A ∪ Bᶜ)ᶜ ∈ L.

  have heq : (A ∪ Bᶜ)ᶜ = B \ A := by
    -- Establish a set-theoretic identity.
    --
    -- By De Morgan's law:
    -- (A ∪ Bᶜ)ᶜ = Aᶜ ∩ B = B \ A.

    ext x
    -- Prove equality by elementwise membership, which is
    -- that two sets are equal if and only if they have exactly the same elements
    -- Goal:
    -- x ∈ (A ∪ Bᶜ)ᶜ ↔ x ∈ B \ A.

    change
      (¬ (x ∈ A ∨ ¬ x ∈ B)) ↔
      (x ∈ B ∧ ¬ x ∈ A)
    -- Expand complement, union, and difference
    -- into their logical meanings.

    tauto
    -- Let Lean automatically prove a statement using basic logic.


  rw [heq] at hcompl
  -- Replace (A ∪ Bᶜ)ᶜ with B \ A.
  -- hcompl now proves B \ A ∈ L.

  exact hcompl
  -- The goal is complete.
  -- Helper 3 is proved.


-- ============================================================
-- HELPER 4: Minimality of the Generated λ-System
-- ============================================================
-- Mathematical statement:
-- If L is a λ-system containing P, then
-- lambdaGen P ⊆ L.
--
-- This follows directly from the definition:
--
-- lambdaGen P is the intersection of all
-- λ-systems containing P.
--
-- Hence lambdaGen P is contained in
-- every eligible λ-system.

private lemma lambdaGen_min
    (P L : Set (Set Ω))
    (hL : IsLambdaSys L)
    (hPL : P ⊆ L) :
    lambdaGen P ⊆ L := by

  intro E hE
  -- Introduce an arbitrary E ∈ lambdaGen P.
  --
  -- E  : Set Ω
  -- hE : E ∈ lambdaGen P
  -- Goal: E ∈ L.

  exact (Set.mem_sInter.mp hE) L ⟨hL, hPL⟩
  -- Since hE established that E belongs to lambdaGen P,
  -- E belongs to every λ-system containing P.
  --
  -- Set.mem_sInter.mp hE:
  -- E belongs to every eligible collection.
  --
  -- Set.mem_sInter.mp:
  -- mp. take the forward direction of an equivalence.
  -- takes a proof that E belongs to an intersection and produces a proof
  -- that E belongs to every collection in that intersection.
  -- L:
  -- Select this particular λ-system.
  -- However, Lean still needs evidence that L qualifies.
  --
  -- ⟨hL, hPL⟩:
  -- Establish that L is eligible:
  -- 1. L is a λ-system.
  -- 2. P ⊆ L.
  --
  -- Therefore E ∈ L.
  -- Since E was arbitrary, lambdaGen P ⊆ L.
  -- Helper 4 is proved.


-- ============================================================
-- HELPER 5: The Good-Sets Construction
-- ============================================================
-- Mathematical statement:
-- Let L be a λ-system and D ∈ L.
-- Define:
--
-- G_D = {B ⊆ Ω | D ∩ B ∈ L}.
--
-- Then G_D is a λ-system.
--
-- We must prove:
-- 1. Ω ∈ G_D.
-- 2. B ∈ G_D implies Bᶜ ∈ G_D.
-- 3. G_D is closed under countable disjoint unions.
--
-- This helper is essential for lambdaGen_inter.

private lemma lambdaSys_good
    (L : Set (Set Ω))
    (hL : IsLambdaSys L)
    (D : Set Ω)
    (hD : D ∈ L) :
    IsLambdaSys {B | D ∩ B ∈ L} := by

  refine {
    -- refine means: I will prove that this collection is a λ-system,
    -- by filling in each required property.
    --
    -- Construct a proof of IsLambdaSys by explicitly
    -- supplying proofs of its three required fields.

    -- --------------------------------------------------------
    -- PROPERTY 1: Universal-set membership
    -- --------------------------------------------------------

    univ_mem := by
      -- Goal: Ω ∈ G_D.
      --
      -- By the definition of G_D, this means:
      -- D ∩ Ω ∈ L.

      change D ∩ univ ∈ L
      -- rewrite the meaning of Ω ∈ G_D as D ∩ Ω ∈ L.
      simpa only [inter_univ] using hD
      -- sima only ... h :
      -- simplify until the goal matches an existing proof.
      -- here simpa only uses this identity to make the goal match hD,
      -- which proves D ∈ L.
      -- inter_univ is the Mathlib identity D ∩ Ω = D,
      -- the goal reduces to D ∈ L.
      -- This is exactly hD.


    -- --------------------------------------------------------
    -- PROPERTY 2: Complement closure
    -- --------------------------------------------------------

    compl_mem := by
      -- Goal:
      -- If B ∈ G_D, prove Bᶜ ∈ G_D.

      intro B hB
      -- Fix an arbitrary B ∈ G_D.
      --
      -- hB : B ∈ G_D.
      -- Goal: Bᶜ ∈ G_D.

      change D ∩ B ∈ L at hB
      -- Expand the definition of G_D in hB.
      -- We now know D ∩ B ∈ L.

      change D ∩ Bᶜ ∈ L
      -- Expand the definition of G_D in the goal.
      -- We must prove D ∩ Bᶜ ∈ L.

      have hd : D \ (D ∩ B) ∈ L :=
        lambda_diff_mem L hL
          (D ∩ B) D hB hD inter_subset_left
      -- USE HELPER 3: lambda_diff_mem.
      --
      -- Let A = D ∩ B and let the larger set be D.
      --
      -- We know:
      -- D ∩ B ∈ L, by hB.
      -- D ∈ L, by hD.
      -- D ∩ B ⊆ D, by inter_subset_left.
      --
      -- Helper 3 gives:
      -- D \ (D ∩ B) ∈ L.

      have heq : D \ (D ∩ B) = D ∩ Bᶜ := by
        -- Prove the set identity:
        -- D \ (D ∩ B) = D ∩ Bᶜ.

        ext x
        -- Prove equality using membership equivalence.

        change
          (x ∈ D ∧ ¬ (x ∈ D ∧ x ∈ B)) ↔
          (x ∈ D ∧ ¬ x ∈ B)
        -- Expand difference and intersection into logic.

        tauto
        -- Verify the logical equivalence.

      rw [heq] at hd
      -- Rewrite D \ (D ∩ B) as D ∩ Bᶜ.
      -- hd now proves D ∩ Bᶜ ∈ L.

      exact hd
      -- This establishes Bᶜ ∈ G_D.
      -- Complement closure is proved.


    -- --------------------------------------------------------
    -- PROPERTY 3: Countable disjoint union closure
    -- --------------------------------------------------------

    iUnion_mem := by
      -- Assume f is a pairwise disjoint sequence
      -- of sets belonging to G_D.
      --
      -- Goal:
      -- (⋃ n, f n) ∈ G_D.

      intro f hdisj hf
      -- f : ℕ → Set Ω
      --
      -- hdisj : Pairwise (Disjoint on f)
      -- hf : ∀ n, f n ∈ G_D
      --
      -- Goal: (⋃ n, f n) ∈ G_D.

      change D ∩ (⋃ n, f n) ∈ L
      -- Expand membership in G_D.
      -- We need:
      -- D ∩ (⋃ n, f n) ∈ L.
      --
      -- We will prove this using distributivity:
      --
      -- D ∩ (⋃ n, f n)
      --   = ⋃ n, (D ∩ f n).


      -- ------------------------------------------------------
      -- STEP 1: Prove the new sequence is pairwise disjoint.
      -- ------------------------------------------------------

      have hd :
          Pairwise (Disjoint on (fun n => D ∩ f n)) := by
        -- Define the sequence g(n) = D ∩ f(n).
        --
        -- We must prove:
        -- For i ≠ j,
        -- (D ∩ f i) and (D ∩ f j) are disjoint.

        intro i j hij
        -- Fix arbitrary distinct indices i and j.
        -- hij : i ≠ j.

        change Disjoint (D ∩ f i) (D ∩ f j)
        -- Express the desired disjointness explicitly.

        apply Set.disjoint_left.mpr
        -- To establish disjointness,
        -- assume a point belongs to both sets
        -- and derive a contradiction.

        intro x hxi hxj
        -- hxi : x ∈ D ∩ f i
        -- hxj : x ∈ D ∩ f j
        --
        -- Therefore:
        -- hxi.2 : x ∈ f i
        -- hxj.2 : x ∈ f j.

        exact Set.disjoint_left.mp
          (hdisj hij) hxi.2 hxj.2
        -- Since i ≠ j, hdisj hij proves
        -- that f i and f j are disjoint.
        --
        -- But x belongs to both f i and f j.
        -- This gives a contradiction.
        --
        -- Hence D ∩ f i and D ∩ f j
        -- are disjoint.


      -- ------------------------------------------------------
      -- STEP 2: Apply countable union closure in L.
      -- ------------------------------------------------------

      have hu : (⋃ n, D ∩ f n) ∈ L :=
        hL.iUnion_mem (fun n => D ∩ f n) hd hf
      -- Apply the λ-system union property to
      -- the sequence g(n) = D ∩ f(n).
      --
      -- hd proves that g is pairwise disjoint.
      --
      -- hf proves that every g(n) belongs to L,
      -- because f(n) ∈ G_D means D ∩ f(n) ∈ L.
      --
      -- Therefore:
      -- ⋃ n, (D ∩ f n) ∈ L.


      -- ------------------------------------------------------
      -- STEP 3: Prove distributivity of intersection.
      -- ------------------------------------------------------

      have heq :
          (⋃ n, D ∩ f n) = D ∩ (⋃ n, f n) := by
        -- Mathematical identity:
        --
        -- ⋃ n, (D ∩ f n)
        --     = D ∩ (⋃ n, f n).
        --
        -- We prove this by showing that an arbitrary
        -- element belongs to the left side iff
        -- it belongs to the right side.

        ext x
        -- Fix an arbitrary x : Ω.
        -- Goal: membership equivalence.

        simp only [Set.mem_iUnion, Set.mem_inter_iff]
        -- Expand indexed-union membership:
        --
        -- x ∈ ⋃ n, E n
        -- iff there exists n with x ∈ E n.
        --
        -- Expand intersection membership:
        --
        -- x ∈ D ∩ E
        -- iff x ∈ D and x ∈ E.

        constructor
        -- Split the equivalence into two implications.
        --
        -- Forward direction: left to right.
        -- Backward direction: right to left.

        case mp =>
          rintro ⟨n, hxD, hxn⟩
          -- Assume x belongs to the left union.
          --
          -- There exists n such that:
          -- hxD : x ∈ D
          -- hxn : x ∈ f n.
          --
          -- We must show:
          -- x ∈ D and x ∈ ⋃ n, f n.

          exact ⟨hxD, ⟨n, hxn⟩⟩
          -- hxD proves x ∈ D.
          -- ⟨n, hxn⟩ proves x ∈ ⋃ n, f n.
          -- Therefore x belongs to the right side.

        case mpr =>
          rintro ⟨hxD, n, hxn⟩
          -- Assume x belongs to the right side.
          --
          -- hxD : x ∈ D
          -- n : ℕ
          -- hxn : x ∈ f n
          --
          -- We must show that x belongs to
          -- at least one D ∩ f n.

          exact ⟨n, hxD, hxn⟩
          -- Choose the same index n.
          -- Since x ∈ D and x ∈ f n,
          -- we have x ∈ D ∩ f n.
          -- Hence x belongs to the left union.


      -- ------------------------------------------------------
      -- STEP 4: Rewrite the union and finish.
      -- ------------------------------------------------------

      rw [heq] at hu
      -- Rewrite:
      --
      -- ⋃ n, (D ∩ f n)
      --     = D ∩ (⋃ n, f n).
      --
      -- hu now proves:
      -- D ∩ (⋃ n, f n) ∈ L.

      exact hu
      -- This matches the goal.
      -- Therefore the union belongs to G_D.
      -- Countable disjoint union closure is proved.
  }

  -- All three defining properties of G_D
  -- have now been established.
  -- Therefore G_D is a λ-system.
  -- Helper 5 is proved.






-- ============================================================
-- LEMMA 1: The Generated λ-System Is a λ-System
-- ============================================================
-- Mathematical statement:
-- Let A be a collection of subsets of Ω.
-- Then lambdaGen A is a λ-system.
--
-- Mathematically:
-- IsLambdaSys (lambdaGen A).
--
-- Proof idea:
-- 1. Recall that lambdaGen A is the intersection
--    of all λ-systems containing A.
-- 2. Prove that Ω belongs to lambdaGen A.
-- 3. Prove that lambdaGen A is closed under complements.
-- 4. Prove that lambdaGen A is closed under
--    countable pairwise disjoint unions.
-- 5. Conclude that lambdaGen A is a λ-system.
--
-- Main principle:
-- An intersection of λ-systems is a λ-system.

lemma lambdaGen_isLambdaSys (A : Set (Set Ω)) :
    IsLambdaSys (lambdaGen A) := by

  constructor
  -- Construct a proof of IsLambdaSys (lambdaGen A).
  -- Lean creates three goals corresponding to
  -- the three defining properties of IsLambdaSys:
  --
  -- Goal 1: Ω ∈ lambdaGen A.
  -- Goal 2: Complement closure.
  -- Goal 3: Countable disjoint union closure.


  -- ----------------------------------------------------------
  -- PROPERTY 1: Universal Set Membership
  -- ----------------------------------------------------------
  -- Mathematical goal:
  -- Ω ∈ lambdaGen A.
  --
  -- Proof idea:
  -- Every λ-system contains Ω.
  -- Therefore Ω belongs to their intersection.

  change univ ∈
      ⋂₀ {L : Set (Set Ω) | IsLambdaSys L ∧ A ⊆ L}
  -- Expand the definition of lambdaGen A.
  --
  -- The expression ⋂₀ denotes the intersection
  -- of a family of collections.
  --
  -- The family consists of all L satisfying:
  -- 1. IsLambdaSys L.
  -- 2. A ⊆ L.
  --
  -- Goal: Prove Ω belongs to this intersection.

  rw [Set.mem_sInter]
  -- Rewrite intersection membership using its definition.
  --
  -- To prove an set belongs to an intersection,
  -- we must show it belongs to every collection
  -- in the family.
  --
  -- New goal:
  -- ∀ t ∈ {L | IsLambdaSys L ∧ A ⊆ L}, univ ∈ t

  intro L hL
  -- Choose an arbitrary collection L.
  --
  -- L : Set (Set Ω)
  -- hL : L ∈ {L | IsLambdaSys L ∧ A ⊆ L}
  --
  -- Goal: univ ∈ L.
  --
  -- The variable t in the previous goal is now
  -- introduced using our chosen name L.

  rcases hL with ⟨hLambda, hAL⟩
  -- Extract the two eligibility conditions.
  --
  -- hLambda : IsLambdaSys L
  -- hAL     : A ⊆ L
  --
  -- Goal: univ ∈ L.

  exact hLambda.univ_mem
  -- Since L is a λ-system, Ω ∈ L.
  --
  -- hLambda.univ_mem supplies the proof.
  --
  -- Because L was arbitrary, Ω belongs to
  -- every λ-system containing A.
  --
  -- Therefore Ω ∈ lambdaGen A.
  -- Property 1 is proved.


  -- ----------------------------------------------------------
  -- PROPERTY 2: Complement Closure
  -- ----------------------------------------------------------
  -- Mathematical statement:
  -- If E ∈ lambdaGen A, then Eᶜ ∈ lambdaGen A.
  --
  -- Proof idea:
  -- 1. Choose an arbitrary E ∈ lambdaGen A.
  -- 2. Choose an arbitrary λ-system L containing A.
  -- 3. Since E belongs to the intersection,
  --    E must belong to L.
  -- 4. Since L is closed under complements,
  --    Eᶜ belongs to L.
  -- 5. Since L was arbitrary,
  --    Eᶜ belongs to lambdaGen A.

  intro E hE
  -- Introduce an arbitrary set E.
  --
  -- E : Set Ω
  -- hE : E ∈ lambdaGen A
  --
  -- Goal: Eᶜ ∈ lambdaGen A.

  change Eᶜ ∈
      ⋂₀ {L : Set (Set Ω) | IsLambdaSys L ∧ A ⊆ L}
  -- Expand the definition of lambdaGen A.
  --
  -- We must show that Eᶜ belongs to the intersection
  -- of all λ-systems containing A.

  rw [Set.mem_sInter]
  -- Rewrite intersection membership as a
  -- universal statement.
  --
  -- New goal:
  -- ∀ t ∈ {L | IsLambdaSys L ∧ A ⊆ L}, Eᶜ ∈ t
  --
  -- This does not prove membership.
  -- It reformulates what remains to be proved.

  intro L hL
  -- Choose an arbitrary collection L from
  -- the family of λ-systems containing A.
  --
  -- Goal: Eᶜ ∈ L.

  rcases hL with ⟨hLambda, hAL⟩
  -- Extract:
  --
  -- hLambda : IsLambdaSys L
  -- hAL     : A ⊆ L
  --
  -- Goal: Eᶜ ∈ L.

  have hEL : E ∈ L := by
    -- Establish the intermediate statement E ∈ L.
    --
    -- We know E ∈ lambdaGen A.
    -- Since lambdaGen A is the intersection of
    -- all eligible λ-systems, E belongs to
    -- every eligible λ-system.
    --
    -- In particular, E belongs to our chosen L.

    exact (Set.mem_sInter.mp hE) L ⟨hLambda, hAL⟩
    -- Set.mem_sInter.mp hE extracts membership
    -- in every eligible collection.
    --
    -- L selects the particular collection.
    --
    -- ⟨hLambda, hAL⟩ establishes that
    -- L is a λ-system containing A.
    --
    -- Therefore E ∈ L.

  exact hLambda.compl_mem E hEL
  -- Apply complement closure of L.
  --
  -- hLambda proves L is a λ-system.
  -- hEL proves E ∈ L.
  --
  -- Therefore Eᶜ ∈ L.
  --
  -- Since L was arbitrary, Eᶜ belongs
  -- to every λ-system containing A.
  --
  -- Hence Eᶜ ∈ lambdaGen A.
  -- Property 2 is proved.


  -- ----------------------------------------------------------
  -- PROPERTY 3: Countable Disjoint Union Closure
  -- ----------------------------------------------------------
  -- Mathematical statement:
  -- Suppose f : ℕ → Set Ω is pairwise disjoint,
  -- and f(n) ∈ lambdaGen A for every n.
  --
  -- Then:
  -- ⋃ n, f(n) ∈ lambdaGen A.
  --
  -- Proof idea:
  -- 1. Introduce the sequence f and its hypotheses.
  -- 2. Choose an arbitrary λ-system L containing A.
  -- 3. Establish that every f(n) belongs to L.
  -- 4. Use pairwise disjointness and the
  --    countable union closure property of L.
  -- 5. Conclude that the union belongs to
  --    every eligible λ-system.
  -- 6. Therefore the union belongs to lambdaGen A.

  intro f hf_disjoint hf_mem
  -- Introduce the sequence and its hypotheses.
  --
  -- f : ℕ → Set Ω
  -- hf_disjoint : Pairwise (Disjoint on f)
  -- hf_mem : ∀ n, f n ∈ lambdaGen A
  --
  -- Goal: (⋃ n, f n) ∈ lambdaGen A.

  change (⋃ n, f n) ∈
      ⋂₀ {L : Set (Set Ω) | IsLambdaSys L ∧ A ⊆ L}
  -- Expand lambdaGen A using its definition.
  --
  -- We must show that the indexed union
  -- belongs to every λ-system containing A.

  rw [Set.mem_sInter]
  -- Rewrite intersection membership.
  --
  -- New goal:
  -- ∀ t ∈ {L | IsLambdaSys L ∧ A ⊆ L},
  --   (⋃ n, f n) ∈ t

  intro L hL
  -- Choose an arbitrary eligible collection L.
  --
  -- Goal: (⋃ n, f n) ∈ L.

  rcases hL with ⟨hLambda, hAL⟩
  -- Extract:
  --
  -- hLambda : IsLambdaSys L
  -- hAL     : A ⊆ L
  --
  -- Goal: (⋃ n, f n) ∈ L.

  have hf_mem_L : ∀ n, f n ∈ L := by
    -- Establish membership of every sequence term in L.
    --
    -- hf_mem says every f(n) belongs to lambdaGen A.
    -- We need to transfer this membership to L.
    --
    -- This is necessary because we will apply
    -- the countable union property of L.

    intro n
    -- Choose an arbitrary n : ℕ.
    --
    -- Goal: f n ∈ L.

    exact (Set.mem_sInter.mp (hf_mem n)) L
        ⟨hLambda, hAL⟩
    -- hf_mem n proves f n ∈ lambdaGen A.
    --
    -- Set.mem_sInter.mp extracts membership
    -- in every eligible λ-system.
    --
    -- L selects our chosen collection.
    -- ⟨hLambda, hAL⟩ proves its eligibility.
    --
    -- Therefore f n ∈ L.
    --
    -- Since n was arbitrary:
    -- ∀ n, f n ∈ L.

  exact hLambda.iUnion_mem f hf_disjoint hf_mem_L
  -- Apply countable disjoint union closure.
  --
  -- f : the indexed sequence of sets.
  -- hf_disjoint : proves pairwise disjointness.
  -- hf_mem_L : proves every f(n) belongs to L.
  --
  -- Since L is a λ-system,
  -- its countable disjoint union belongs to L.
  --
  -- As L was arbitrary, the union belongs
  -- to every λ-system containing A.
  --
  -- Hence (⋃ n, f n) ∈ lambdaGen A.
  --
  -- Property 3 is proved.
  -- Therefore lambdaGen A is a λ-system.
  -- Lemma 1 is complete.


-- ============================================================
-- LEMMA 2: The generated class contains its generators
-- ============================================================
-- Mathematical statement:
-- Let A be a collection of subsets of Ω.
-- Then A ⊆ lambdaGen A.
--
-- Equivalently:
-- For every E ∈ A, E ∈ lambdaGen A.
--
-- Proof idea:
-- 1. Choose an arbitrary E ∈ A.
-- 2. Expand lambdaGen A as an intersection
--    of all λ-systems containing A.
-- 3. Choose an arbitrary eligible λ-system L.
-- 4. By eligibility, A ⊆ L.
-- 5. Since E ∈ A, conclude E ∈ L.
-- 6. Because L was arbitrary,
--    E ∈ lambdaGen A.
-- 7. Therefore A ⊆ lambdaGen A.
--
-- Important:
-- We only use set inclusion in this proof.
-- No closure property of a λ-system is required.

lemma subset_lambdaGen (A : Set (Set Ω)) :
    A ⊆ lambdaGen A := by

  intro E hE
  -- Introduce an arbitrary E ∈ A.
  --
  -- E : Set Ω
  -- hE : E ∈ A
  --
  -- Goal: E ∈ lambdaGen A.
  --
  -- Recall:
  -- In Lemma 1, Property 2, hE meant
  -- E ∈ lambdaGen A.
  --
  -- Here hE means E ∈ A.
  -- The meaning of a hypothesis depends
  -- on the current theorem and goal.

  change E ∈
      ⋂₀ {L : Set (Set Ω) | IsLambdaSys L ∧ A ⊆ L}
  -- Expand the definition of lambdaGen A.
  --
  -- Goal:
  -- E belongs to the intersection of all
  -- λ-systems containing A.

  rw [Set.mem_sInter]
  -- Rewrite intersection membership using its definition.
  --
  -- New goal:
  -- ∀ t ∈ {L | IsLambdaSys L ∧ A ⊆ L}, E ∈ t
  --
  -- We must prove that E belongs to
  -- every eligible collection.

  intro L hL
  -- Choose an arbitrary eligible collection L.
  --
  -- L : Set (Set Ω)
  -- hL : L ∈ {L | IsLambdaSys L ∧ A ⊆ L}
  --
  -- Goal: E ∈ L.

  rcases hL with ⟨hLambda, hAL⟩
  -- Extract the eligibility conditions:
  --
  -- hLambda : IsLambdaSys L
  -- hAL     : A ⊆ L
  --
  -- Goal: E ∈ L.
  --
  -- We will use hAL, since the proof
  -- only requires the inclusion A ⊆ L.

  exact hAL hE
  -- hAL : A ⊆ L.
  --
  -- By the definition of subset:
  -- For every E, if E ∈ A, then E ∈ L.
  --
  -- hE : E ∈ A.
  --
  -- Applying hAL to hE produces a proof of E ∈ L.
  --
  -- Since L was arbitrary, E belongs
  -- to every λ-system containing A.
  --
  -- Therefore E ∈ lambdaGen A.
  --
  -- Since E ∈ A was arbitrary,
  -- A ⊆ lambdaGen A.
  -- Lemma 2 is proved.


-- ============================================================
-- LEMMA 3: λ(P) is cloosed under intersections
-- ============================================================
-- Mathematical statement:
-- Let P be a π-system. Then lambdaGen P is closed under finite intersections.
--
-- In particular:
-- If A, B ∈ lambdaGen P, then A ∩ B ∈ lambdaGen P.
--
-- Proof idea:
-- 1. Establish that lambdaGen P is a λ-system.
-- 2. Establish that P ⊆ lambdaGen P.
-- 3. Stage 1: Prove that if D ∈ P and
--    B ∈ lambdaGen P, then D ∩ B ∈ lambdaGen P.
-- 4. Construct a good-set λ-system using Helper 5.
-- 5. Use the π-system property and Helper 4
--    to complete Stage 1.
-- 6. Stage 2: Choose A, B ∈ lambdaGen P.
-- 7. Construct another good-set λ-system.
-- 8. Use Stage 1 and intersection commutativity
--    to show this family contains P.
-- 9. Apply Helper 4 again to obtain
--    A ∩ B ∈ lambdaGen P.
--
-- Why two stages?
-- The π-system property only guarantees
-- intersection closure when BOTH sets belong to P.
--
-- Stage 1 extends the second argument to lambdaGen P.
-- Stage 2 extends the first argument to lambdaGen P.

lemma lambdaGen_inter (P : Set (Set Ω))
    (hP : IsPiSys P) :
    ∀ A ∈ lambdaGen P, ∀ B ∈ lambdaGen P,
      A ∩ B ∈ lambdaGen P := by

  -- ----------------------------------------------------------
  -- PREPARATION: Establish two known properties.
  -- ----------------------------------------------------------

  have hK : IsLambdaSys (lambdaGen P) :=
    lambdaGen_isLambdaSys P
  -- USE LEMMA 1.
  -- hK establishes that lambdaGen P is a λ-system.
  -- This allows us to apply Helper 5.

  have hPK : P ⊆ lambdaGen P :=
    subset_lambdaGen P
  -- USE LEMMA 2.
  -- hPK establishes that the original π-system P
  -- is contained in its generated λ-system.
  -- Therefore:
  -- If D ∈ P, then D ∈ lambdaGen P.


  -- ----------------------------------------------------------
  -- STAGE 1: One Set Belongs to the Original π-System
  -- ----------------------------------------------------------
  -- Mathematical goal:
  --
  -- ∀ D ∈ P, ∀ B ∈ lambdaGen P,
  --   D ∩ B ∈ lambdaGen P.
  --
  -- We fix D ∈ P and construct:
  --
  -- G_D = {B | D ∩ B ∈ lambdaGen P}.
  --
  -- We will prove:
  -- 1. G_D is a λ-system.
  -- 2. P ⊆ G_D.
  -- 3. Therefore lambdaGen P ⊆ G_D.

  have hfirst :
      ∀ D ∈ P, ∀ B ∈ lambdaGen P,
        D ∩ B ∈ lambdaGen P := by
    -- hfirst is the name assigned to its proof.
    -- We must establish the proposition before
    -- using it in Stage 2.

    intro D hD
    -- Introduce arbitrary D ∈ P.
    -- D : Set Ω
    -- hD : D ∈ P
    --
    -- Goal:
    -- ∀ B ∈ lambdaGen P, D ∩ B ∈ lambdaGen P.
    --
    -- We do not introduce B yet.
    -- Instead, we construct a good-set family.

    have hgood :
        IsLambdaSys {B | D ∩ B ∈ lambdaGen P} :=
      lambdaSys_good (lambdaGen P) hK D (hPK hD)
    -- USE HELPER 5: lambdaSys_good.
    --
    -- Define:
    -- G_D = {B | D ∩ B ∈ lambdaGen P}.
    --
    -- Helper 5 requires:
    -- 1. A λ-system L.
    -- 2. A proof that L is a λ-system.
    -- 3. A fixed set D.
    -- 4. A proof that D ∈ L.
    --
    -- Here:
    -- L = lambdaGen P.
    -- hK proves IsLambdaSys (lambdaGen P).
    -- D is the fixed set.
    -- hPK hD proves D ∈ lambdaGen P.
    --
    -- Therefore G_D is a λ-system.

    have hcontains :
        P ⊆ {B | D ∩ B ∈ lambdaGen P} := by
      -- Goal: P ⊆ G_D.
      --
      -- We must show that every set in P also belongs to G_D.

      intro B hB
      -- Introduce arbitrary B ∈ P.
      --
      -- hB : B ∈ P.
      --
      -- Goal:
      -- D ∩ B ∈ lambdaGen P.
      --
      -- Recall hD : D ∈ P.

      exact hPK (hP D hD B hB)
      -- hP states that P is a π-system.
      --
      -- Applying hP to D and B gives:
      -- D ∩ B ∈ P.
      --
      -- hPK : P ⊆ lambdaGen P.
      --
      -- Applying hPK gives:
      -- D ∩ B ∈ lambdaGen P.
      --
      -- Therefore B ∈ G_D.
      -- Since B was arbitrary, P ⊆ G_D.

    exact lambdaGen_min P
      {B | D ∩ B ∈ lambdaGen P}
      hgood hcontains
    -- USE HELPER 4: lambdaGen_min.
    --
    -- We know:
    -- hgood proves G_D is a λ-system.
    -- hcontains proves P ⊆ G_D.
    --
    -- By minimality: lambdaGen P ⊆ G_D.
    --
    -- Thus every B ∈ lambdaGen P belongs to G_D.
    --
    -- By the definition of G_D:
    -- D ∩ B ∈ lambdaGen P.
    --
    -- Since D ∈ P was arbitrary,
    -- Stage 1 is proved.
    --
    -- hfirst is now available for use in Stage 2.


  -- ----------------------------------------------------------
  -- STAGE 2: Both Sets Belong to lambdaGen P
  -- ----------------------------------------------------------
  -- Mathematical goal:
  --
  -- ∀ A ∈ lambdaGen P, ∀ B ∈ lambdaGen P,
  --   A ∩ B ∈ lambdaGen P.
  --
  -- Fix A ∈ lambdaGen P and define:
  --
  -- G_A = {D | A ∩ D ∈ lambdaGen P}.
  --
  -- We will prove:
  -- 1. G_A is a λ-system.
  -- 2. P ⊆ G_A, using Stage 1.
  -- 3. lambdaGen P ⊆ G_A, by minimality.
  -- 4. Since B ∈ lambdaGen P, B ∈ G_A.
  -- 5. Therefore A ∩ B ∈ lambdaGen P.

  intro A hA B hB
  -- Introduce arbitrary A, B ∈ lambdaGen P.
  -- A : Set Ω
  -- hA : A ∈ lambdaGen P
  --
  -- B : Set Ω
  -- hB : B ∈ lambdaGen P
  --
  -- Goal: A ∩ B ∈ lambdaGen P.

  have hgood :
      IsLambdaSys {D | A ∩ D ∈ lambdaGen P} :=
    lambdaSys_good (lambdaGen P) hK A hA
  -- USE HELPER 5 AGAIN.
  --
  -- Define:
  -- G_A = {D | A ∩ D ∈ lambdaGen P}.
  --
  -- Helper 5 applies because:
  -- lambdaGen P is a λ-system, by hK.
  -- A belongs to lambdaGen P, by hA.
  --
  -- Therefore G_A is a λ-system.

  have hcontains :
      P ⊆ {D | A ∩ D ∈ lambdaGen P} := by
    -- Goal: P ⊆ G_A.
    --
    -- We need to show:
    -- If D ∈ P, then A ∩ D ∈ lambdaGen P.

    intro D hD
    -- Introduce arbitrary D ∈ P.
    -- hD : D ∈ P.
    --
    -- Goal: D ∈ G_A.
    -- Equivalently:
    -- A ∩ D ∈ lambdaGen P.

    change A ∩ D ∈ lambdaGen P
    -- Express membership in G_A explicitly.
    --
    -- The goal is definitionally equal to
    -- A ∩ D ∈ lambdaGen P.

    simpa only [inter_comm] using hfirst D hD A hA
    -- USE STAGE 1: hfirst.
    --
    -- Recall:
    -- hfirst :
    -- ∀ D ∈ P, ∀ B ∈ lambdaGen P,
    --   D ∩ B ∈ lambdaGen P.
    --
    -- We apply hfirst with:
    -- D = D, using hD : D ∈ P.
    -- B = A, using hA : A ∈ lambdaGen P.
    --
    -- This gives:
    -- D ∩ A ∈ lambdaGen P.
    --
    -- But our current goal is:
    -- A ∩ D ∈ lambdaGen P.
    --
    -- inter_comm states D ∩ A = A ∩ D.
    --
    -- simpa rewrites the intersection
    -- and completes the goal.
    --
    -- Hence P ⊆ G_A.

  have hsub :
      lambdaGen P ⊆ {D | A ∩ D ∈ lambdaGen P} :=
    lambdaGen_min P
      {D | A ∩ D ∈ lambdaGen P}
      hgood hcontains
  -- USE HELPER 4 AGAIN.
  --
  -- hgood proves G_A is a λ-system.
  -- hcontains proves P ⊆ G_A.
  --
  -- By minimality of lambdaGen P:
  -- lambdaGen P ⊆ G_A.
  --
  -- This is stored as hsub.

  exact hsub hB
  -- hsub : lambdaGen P ⊆ G_A.
  -- hB : B ∈ lambdaGen P.
  --
  -- Applying hsub to hB gives:
  -- B ∈ G_A.
  --
  -- By the definition of G_A:
  -- A ∩ B ∈ lambdaGen P.
  --
  -- Since A and B were arbitrary,
  -- lambdaGen P is closed under intersections.
  --
  -- Lemma 3 is proved.



-- ============================================================
-- HELPER 6: Intersection Closure Implies Finite Union Closure
-- ============================================================
-- Mathematical statement:
-- Let L be a λ-system that is closed under intersections.
-- If A, B ∈ L, then A ∪ B ∈ L.
--
-- Proof idea:
-- 1. Since A, B ∈ L, complement closure gives
--    Aᶜ ∈ L and Bᶜ ∈ L.
-- 2. Since L is closed under intersections,
--    Aᶜ ∩ Bᶜ ∈ L.
-- 3. Complement closure gives (Aᶜ ∩ Bᶜ)ᶜ ∈ L.
-- 4. By De Morgan's law,
--    (Aᶜ ∩ Bᶜ)ᶜ = A ∪ B.
-- 5. Therefore A ∪ B ∈ L.

private lemma lambda_union_mem_of_inter_closed
    (L : Set (Set Ω))
    (hL : IsLambdaSys L)
    (hπ : ∀ A ∈ L, ∀ B ∈ L, A ∩ B ∈ L)
    (A B : Set Ω)
    (hA : A ∈ L)
    (hB : B ∈ L) :
    A ∪ B ∈ L := by
  -- Goal: A ∪ B ∈ L.
  -- hπ is the additional intersection-closure assumption.
  -- It does not follow from the λ-system axioms alone.

  have hi : Aᶜ ∩ Bᶜ ∈ L :=
    hπ Aᶜ (hL.compl_mem A hA)
      Bᶜ (hL.compl_mem B hB)
  -- First, complement closure gives Aᶜ ∈ L and Bᶜ ∈ L.
  -- Apply hπ to those two sets.
  -- Therefore Aᶜ ∩ Bᶜ ∈ L.
  -- hi can be read as "h intersection".

  have hc : (Aᶜ ∩ Bᶜ)ᶜ ∈ L :=
    hL.compl_mem (Aᶜ ∩ Bᶜ) hi
  -- Apply complement closure to Aᶜ ∩ Bᶜ.
  -- We obtain (Aᶜ ∩ Bᶜ)ᶜ ∈ L.
  -- hc can be read as "h complement".

  simpa only [compl_inter, compl_compl] using hc
  -- compl_inter applies De Morgan's law.
  -- compl_compl simplifies double complements.
  -- (Aᶜ ∩ Bᶜ)ᶜ = A ∪ B.
  -- Hence A ∪ B ∈ L.
  -- Helper 6 is proved.


-- ============================================================
-- HELPER 7: Arbitrary Countable Union Closure
-- ============================================================
-- Mathematical statement:
-- Let L be a λ-system closed under finite intersections.
-- If f(n) ∈ L for every n ∈ ℕ, then
-- ⋃ n, f(n) ∈ L.
--
-- Proof idea:
-- 1. Construct finite accumulated unions:
--    u(n) = ⋃_{k<n} f(k).
-- 2. Prove u(n) ∈ L using induction and Helper 6.
-- 3. Define the disjointified sequence:
--    d(n) = f(n) \ u(n).
-- 4. Prove every d(n) belongs to L.
-- 5. Prove the sets d(n) are pairwise disjoint.
-- 6. Show ⋃ n, d(n) = ⋃ n, f(n).
-- 7. Apply countable disjoint union closure.
-- 8. Conclude ⋃ n, f(n) ∈ L.
--
-- Important:
-- The original sequence f need not be pairwise disjoint.
-- We construct d to satisfy the disjointness requirement.

private lemma lambda_iUnion_mem_of_inter_closed
    (L : Set (Set Ω))
    (hL : IsLambdaSys L)
    (hπ : ∀ A ∈ L, ∀ B ∈ L, A ∩ B ∈ L)
    (f : ℕ → Set Ω)
    (hf : ∀ n, f n ∈ L) :
    (⋃ n, f n) ∈ L := by

  -- ----------------------------------------------------------
  -- STEP 1: Construct the finite accumulated unions.
  -- ----------------------------------------------------------

  let u : ℕ → Set Ω :=
    fun n => Nat.rec ∅ (fun k S => S ∪ f k) n
  -- Nat.rec defines u recursively.
  -- u(0) = ∅.
  -- u(n+1) = u(n) ∪ f(n).
  -- Therefore u(n) is the union of the first n sets:
  -- u(n) = ⋃_{k<n} f(k).

  -- ----------------------------------------------------------
  -- STEP 2: Prove every finite union belongs to L.
  -- ----------------------------------------------------------

  have hu : ∀ n, u n ∈ L := by
    intro n
    -- Fix an arbitrary n.
    -- Goal: u n ∈ L.

    induction n with
    -- Use induction on n.
    -- Base case: n = 0.
    -- Induction step: n → n+1.

    | zero =>
        change (∅ : Set Ω) ∈ L
        -- Since u(0) = ∅, our goal becomes ∅ ∈ L.

        exact lambda_empty_mem L hL
        -- USE HELPER 1.
        -- Every λ-system contains the empty set.

    | succ n ih =>
        -- ih : u n ∈ L.
        -- Goal: u (n+1) ∈ L.

        change u n ∪ f n ∈ L
        -- By recursive definition:
        -- u(n+1) = u(n) ∪ f(n).

        exact lambda_union_mem_of_inter_closed
          L hL hπ (u n) (f n) ih (hf n)
        -- USE HELPER 6.
        -- ih proves u(n) ∈ L.
        -- hf n proves f(n) ∈ L.
        -- Finite union closure gives u(n+1) ∈ L.

  -- ----------------------------------------------------------
  -- STEP 3: Earlier sets are contained in u(n).
  -- ----------------------------------------------------------

  have hprior : ∀ n k, k < n → f k ⊆ u n := by
    -- Mathematical goal:
    -- If k < n, then f(k) ⊆ u(n).
    --
    -- This follows because u(n) contains all sets
    -- whose indices are smaller than n.

    intro n
    induction n with

    | zero =>
        intro k hk
        -- hk : k < 0.
        -- This is impossible for natural numbers.

        omega
        -- omega proves the arithmetic contradiction.

    | succ n ih =>
        intro k hk x hx
        -- hk : k < n+1.
        -- hx : x ∈ f(k).
        -- Goal: x ∈ u(n+1).

        change x ∈ u n ∪ f n
        -- Expand u(n+1) into u(n) ∪ f(n).

        by_cases hkn : k = n

        case pos =>
          subst k
          -- Replace k with n.
          -- hx now proves x ∈ f(n).

          exact Or.inr hx
          -- Membership in f(n) implies
          -- membership in u(n) ∪ f(n).

        case neg =>
          exact Or.inl (ih k (by omega) hx)
          -- Since k < n+1 and k ≠ n,
          -- omega establishes k < n.
          --
          -- The induction hypothesis proves x ∈ u(n).
          -- Hence x ∈ u(n) ∪ f(n).

  -- ----------------------------------------------------------
  -- STEP 4: Construct the disjointified sequence.
  -- ----------------------------------------------------------

  let d : ℕ → Set Ω :=
    fun n => f n ∩ (u n)ᶜ
  -- d(n) = f(n) \ u(n).
  --
  -- It contains elements of f(n) that do not belong
  -- to any earlier set f(k), where k < n.
  --
  -- Therefore repeated elements are assigned
  -- only to their earliest occurrence.

  -- ----------------------------------------------------------
  -- STEP 5: Prove every d(n) belongs to L.
  -- ----------------------------------------------------------

  have hdmem : ∀ n, d n ∈ L := by
    intro n
    -- Fix arbitrary n.
    -- Goal: d(n) ∈ L.

    exact hπ (f n) (hf n) ((u n)ᶜ)
      (hL.compl_mem (u n) (hu n))
    -- hf n proves f(n) ∈ L.
    -- hu n proves u(n) ∈ L.
    -- Complement closure gives u(n)ᶜ ∈ L.
    -- Intersection closure then gives
    -- f(n) ∩ u(n)ᶜ ∈ L.
    -- Thus d(n) ∈ L.

  -- ----------------------------------------------------------
  -- STEP 6: Prove the sequence d is pairwise disjoint.
  -- ----------------------------------------------------------

  have hdisj : Pairwise (Disjoint on d) := by
    -- Goal:
    -- For i ≠ j, d(i) ∩ d(j) = ∅.

    intro i j hij
    -- Introduce distinct indices i and j.
    -- hij : i ≠ j.

    change Disjoint (d i) (d j)
    -- Express the disjointness goal explicitly.

    apply Set.disjoint_left.mpr
    -- Prove disjointness by contradiction.
    -- Assume an element belongs to both sets.

    intro x hxi hxj
    -- hxi : x ∈ d(i).
    -- hxj : x ∈ d(j).

    change x ∈ f i ∧ x ∉ u i at hxi
    change x ∈ f j ∧ x ∉ u j at hxj
    -- Expand the definition of d.
    --
    -- hxi.1 : x ∈ f(i)
    -- hxi.2 : x ∉ u(i)
    -- hxj.1 : x ∈ f(j)
    -- hxj.2 : x ∉ u(j)

    rcases lt_or_gt_of_ne hij with hlt | hgt
    -- Since i ≠ j, either i < j or i > j.

    case inl =>
      -- Case i < j.
      -- Because f(i) is an earlier set,
      -- hprior gives f(i) ⊆ u(j).

      exact hxj.2 (hprior j i hlt hxi.1)
      -- hxi.1 proves x ∈ f(i).
      -- hprior gives x ∈ u(j).
      -- But hxj.2 states x ∉ u(j).
      -- Contradiction.

    case inr =>
      -- Case i > j.
      -- Now f(j) is an earlier set than f(i).

      exact hxi.2 (hprior i j hgt hxj.1)
      -- hxj.1 proves x ∈ f(j).
      -- hprior gives x ∈ u(i).
      -- But hxi.2 states x ∉ u(i).
      -- Contradiction.

  -- ----------------------------------------------------------
  -- STEP 7: Show every finite union is covered by d.
  -- ----------------------------------------------------------

  have hcover : ∀ n, u n ⊆ ⋃ k, d k := by
    -- Goal: Every element that has appeared among
    -- the first n sets belongs to some d(k).

    intro n
    induction n with

    | zero =>
        intro x hx
        -- Since u(0) = ∅, this case is impossible.

        change x ∈ (∅ : Set Ω) at hx
        exact hx.elim
        -- Empty-set membership yields a contradiction.

    | succ n ih =>
        intro x hx
        change x ∈ u n ∪ f n at hx
        -- An element of u(n+1) is either
        -- in u(n) or in f(n).

        rcases hx with hx | hx

        case inl =>
          exact ih hx
          -- If x already belongs to u(n),
          -- the induction hypothesis proves
          -- x belongs to some d(k).

        case inr =>
          rcases Classical.em (x ∈ u n) with hxold | hxnew
          -- Apply the law of excluded middle.
          -- Either x was already in u(n), or it was not.

          case inl =>
            exact ih hxold
            -- If x appeared earlier, use the
            -- induction hypothesis.

          case inr =>
            exact Set.mem_iUnion.mpr
              ⟨n, ⟨hx, hxnew⟩⟩
            -- Here x ∈ f(n) and x ∉ u(n).
            -- Therefore x ∈ d(n).
            -- Choosing index n proves union membership.

  -- ----------------------------------------------------------
  -- STEP 8: Prove the two countable unions are equal.
  -- ----------------------------------------------------------

  have hforward : (⋃ n, d n) ⊆ ⋃ n, f n := by
    -- Prove that every element of the disjointified
    -- union belongs to the original union.

    intro x hx

    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    -- Choose n such that x ∈ d(n).

    change x ∈ f n ∧ x ∉ u n at hxn
    -- Since d(n) ⊆ f(n), we know x ∈ f(n).

    exact Set.mem_iUnion.mpr ⟨n, hxn.1⟩
    -- Use n as the witness.
    -- Hence x belongs to the original union.

  have hbackward : (⋃ n, f n) ⊆ ⋃ n, d n := by
    -- Prove every element of the original union
    -- belongs to the disjointified union.

    intro x hx

    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    -- Choose n such that x ∈ f(n).

    rcases Classical.em (x ∈ u n) with hxold | hxnew
    -- Case distinction:
    -- x appeared earlier, or x is new at index n.

    case inl =>
      exact hcover n hxold
      -- If x already appeared, hcover proves
      -- that x belongs to some d(k).

    case inr =>
      exact Set.mem_iUnion.mpr
        ⟨n, ⟨hxn, hxnew⟩⟩
      -- If x did not appear earlier,
      -- then x ∈ f(n) \ u(n) = d(n).
      -- Hence x belongs to the disjointified union.

  have heq : (⋃ n, d n) = ⋃ n, f n :=
    Set.Subset.antisymm hforward hbackward
  -- Mutual inclusion gives equality:
  -- ⋃ n, d(n) = ⋃ n, f(n).

  -- ----------------------------------------------------------
  -- STEP 9: Apply the λ-system union property.
  -- ----------------------------------------------------------

  have hUnion : (⋃ n, d n) ∈ L :=
    hL.iUnion_mem d hdisj hdmem
  -- Apply countable disjoint union closure.
  -- hdisj proves d is pairwise disjoint.
  -- hdmem proves every d(n) belongs to L.
  -- Therefore ⋃ n, d(n) ∈ L.

  rw [heq] at hUnion
  -- Replace ⋃ n, d(n) with ⋃ n, f(n).
  -- hUnion now proves the original union belongs to L.

  exact hUnion
  -- Therefore ⋃ n, f(n) ∈ L.
  -- Helper 7 is proved.



-- ============================================================
-- LEMMA: A λ-System that is a π-system Is a σ-Field
-- ============================================================
-- Mathematical statement:
-- Let L be a λ-system closed under finite intersections.
-- Then L is a σ-field (σ-algebra).
--
-- Proof idea:
-- 1. A λ-system contains Ω.
-- 2. A λ-system is closed under complements.
-- 3. Helper 7 establishes arbitrary countable union closure.
-- 4. These are the defining properties of a σ-field.

lemma isSigmaField_of_lambda_pi
    (L : Set (Set Ω))
    (hL : IsLambdaSys L)
    (hπ : ∀ A ∈ L, ∀ B ∈ L, A ∩ B ∈ L) :
    IsSigmaField L := by

  constructor
  -- Construct IsSigmaField L by proving
  -- each of its three required properties.
  -- proprty 1: Universal-set membership.
  -- property 2: Complement closure.
  -- property 3: Arbitrary countable union closure.

  -- ----------------------------------------------------------
  -- PROPERTY 1: Universal-set membership.
  -- ----------------------------------------------------------

  case univ_mem =>
    exact hL.univ_mem
    -- L is a λ-system.
    -- Therefore Ω ∈ L.

  -- ----------------------------------------------------------
  -- PROPERTY 2: Complement closure.
  -- ----------------------------------------------------------

  case compl_mem =>
    intro A hA
    -- Let A ∈ L.
    -- Goal: Aᶜ ∈ L.

    exact hL.compl_mem A hA
    -- Apply λ-system complement closure.

  -- ----------------------------------------------------------
  -- PROPERTY 3: Arbitrary countable union closure.
  -- ----------------------------------------------------------

  case iUnion_mem =>
    intro f hf
    -- f : ℕ → Set Ω
    -- hf : ∀ n, f(n) ∈ L.
    -- Goal: ⋃ n, f(n) ∈ L.
    --
    -- Unlike the λ-system union property,
    -- the sets f(n) need not be pairwise disjoint.

    exact lambda_iUnion_mem_of_inter_closed
      L hL hπ f hf
    -- USE HELPER 7.
    -- Since L is a λ-system closed under intersections,
    -- Helper 7 establishes arbitrary countable union closure.
    -- Therefore L satisfies all σ-field properties.


-- ============================================================
-- FINAL THEOREM: The π–λ Theorem
-- ============================================================
-- Mathematical statement:
-- Let P be a π-system and L be a λ-system.
-- If P ⊆ L, then σ(P) ⊆ L.
--
-- In other words:
-- Every λ-system containing a π-system P
-- must also contain the σ-field generated by P.
--
-- Proof idea:
-- 1. Prove lambdaGen P is a σ-field.
--    Use lambdaGen_isLambdaSys, lambdaGen_inter,
--    and isSigmaField_of_lambda_pi.
-- 2. Prove P ⊆ lambdaGen P.
-- 3. By λ-system minimality, lambdaGen P ⊆ L.
-- 4. Since lambdaGen P is a σ-field containing P,
--    minimality of sigmaGen gives
--    sigmaGen P ⊆ lambdaGen P.
-- 5. Combine both inclusions to obtain
--    sigmaGen P ⊆ L.

theorem pi_lambda
    (P L : Set (Set Ω))
    (hP : IsPiSys P)
    (hL : IsLambdaSys L)
    (hPL : P ⊆ L) :
    sigmaGen P ⊆ L := by

  -- ----------------------------------------------------------
  -- STEP 1: Prove lambdaGen P is a σ-field.
  -- ----------------------------------------------------------

  have hK : IsSigmaField (lambdaGen P) :=
    isSigmaField_of_lambda_pi (lambdaGen P)
      (lambdaGen_isLambdaSys P)
      (lambdaGen_inter P hP)
  -- lambdaGen_isLambdaSys proves lambdaGen P
  -- is a λ-system.
  --
  -- lambdaGen_inter proves lambdaGen P
  -- is closed under intersections.
  --
  -- isSigmaField_of_lambda_pi combines these
  -- results to establish that lambdaGen P
  -- is a σ-field.

  -- ----------------------------------------------------------
  -- STEP 2: Establish P ⊆ lambdaGen P.
  -- ----------------------------------------------------------

  have hPK : P ⊆ lambdaGen P :=
    subset_lambdaGen P
  -- Use the previously proved inclusion lemma.
  -- Every generator belongs to the generated λ-system.

  -- ----------------------------------------------------------
  -- STEP 3: Establish lambdaGen P ⊆ L.
  -- ----------------------------------------------------------

  have hKL : lambdaGen P ⊆ L :=
    lambdaGen_min P L hL hPL
  -- USE HELPER 4: Minimality.
  --
  -- hL proves L is a λ-system.
  -- hPL proves P ⊆ L.
  --
  -- Therefore the smallest λ-system containing P
  -- must be contained in L.

  -- ----------------------------------------------------------
  -- STEP 4: Introduce an arbitrary E ∈ sigmaGen P.
  -- ----------------------------------------------------------

  intro E hE
  -- E : Set Ω
  -- hE : E ∈ sigmaGen P
  -- Goal: E ∈ L.

  -- ----------------------------------------------------------
  -- STEP 5: Prove E ∈ lambdaGen P.
  -- ----------------------------------------------------------

  have hEK : E ∈ lambdaGen P :=
    (Set.mem_sInter.mp hE)
      (lambdaGen P) ⟨hK, hPK⟩
  -- sigmaGen P is the intersection of all
  -- σ-fields containing P.
  --
  -- Set.mem_sInter.mp hE gives membership
  -- in every such σ-field.
  --
  -- lambdaGen P is one of those σ-fields:
  -- hK proves it is a σ-field.
  -- hPK proves that it contains P.
  --
  -- Therefore E ∈ lambdaGen P.

  -- ----------------------------------------------------------
  -- STEP 6: Conclude E ∈ L.
  -- ----------------------------------------------------------

  exact hKL hEK
  -- hKL proves lambdaGen P ⊆ L.
  -- hEK proves E ∈ lambdaGen P.
  --
  -- Applying hKL to hEK proves E ∈ L.
  -- Since E ∈ sigmaGen P was arbitrary,
  -- sigmaGen P ⊆ L.
  --
  -- The π–λ theorem is proved.

end Math7800.Midterm

#print axioms Math7800.Midterm.lambdaGen_isLambdaSys
#print axioms Math7800.Midterm.subset_lambdaGen
#print axioms Math7800.Midterm.lambdaGen_inter
#print axioms Math7800.Midterm.isSigmaField_of_lambda_pi
#print axioms Math7800.Midterm.pi_lambda
