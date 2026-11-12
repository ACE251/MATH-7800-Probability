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

/-! ## A1：λ(A) 是 λ-系统 -/
-- ============================================================
-- LEMMA 1: (A1) The Generated λ-System Is a λ-System
-- ============================================================
-- Mathematical statement:
-- Let A be a collection of subsets of Ω.
-- Then lambdaGen A is a λ-system.

/-- L₀ = λ(P) 是 λ-系统：它是所有包含 P 的 λ-系统的交，三条性质在每一个里都成立。
--λ(A) 的定义是 ⋂₀ {L | L 是 λ-系统 且 A ⊆ L}
`mem_sInter : x ∈ ⋂₀ S ↔ ∀ t ∈ S, x ∈ t`；`hL.1`：L 是 λ-系统；`hL.2`：A ⊆ L。 -/
lemma lambdaGen_isLambdaSys (A : Set (Set Ω)) : IsLambdaSys (lambdaGen A) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (λ₁)
    exact mem_sInter.2 fun L hL => hL.1.univ_mem  --只需证对每个 L，Ω ∈ L
  · -- (λ₂)
    intro B hB
    exact mem_sInter.2 fun L hL => hL.1.compl_mem B ((mem_sInter.1 hB) L hL)
  · -- (λ₃)
    intro f hd hf
    exact mem_sInter.2 fun L hL =>
      hL.1.iUnion_mem f hd (fun n => mem_sInter.1 (hf n) L hL)


/-! ## A2：A ⊆ λ(A) -/
-- ============================================================
-- LEMMA 2: The generated class contains its generators
-- ============================================================
-- Mathematical statement:
-- Let A be a collection of subsets of Ω.
-- Then A ⊆ lambdaGen A.

/-- P ⊆ L₀：P 包含在每个包含 P 的 λ-系统里。 -/
lemma subset_lambdaGen (A : Set (Set Ω)) : A ⊆ lambdaGen A := by
  intro B hB
  exact mem_sInter.2 fun L hL => hL.2 hB

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
-- LEMMA 3: (A3) λ(P) is cloosed under intersections
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
-- LEMMA: (A4) A λ-System that is a π-system Is a σ-Field
-- ============================================================
-- Mathematical statement:
-- Let L be a λ-system closed under finite intersections.
-- Then L is a σ-field (σ-algebra).
--

lemma isSigmaField_of_lambda_pi (L : Set (Set Ω)) (hL : IsLambdaSys L)
    (hπ : ∀ A ∈ L, ∀ B ∈ L, A ∩ B ∈ L) : IsSigmaField L := by
  refine ⟨?_, ?_, ?_⟩ -- Break the proof into 3 parts
  · exact hL.univ_mem

  · exact hL.compl_mem

  · intro f hf
    -- ⋃ f equals the union of its disjointed version
    rw [← iUnion_disjointed]
    -- λ-systems contain disjoint unions; disjointed f is pairwise disjoint
    apply hL.iUnion_mem (disjointed f) (disjoint_disjointed f)
    -- still to show: each piece disjointed f n is in L
    intro n
    -- disjointed f n is f n with earlier f i's removed one at a time,
    -- so it is enough that L survives "t ↦ t \ f i"
    -- Prove recursivly
    refine disjointedRec (p := (· ∈ L)) ?_ (hf n)
    intro t i ht
    -- t \ f i = t ∩ (f i)ᶜ, which is in L by hπ and compl_mem
    rw [sdiff_eq]
    exact hπ t ht (f i)ᶜ (hL.compl_mem (f i) (hf i))






-- ============================================================
-- FINAL THEOREM: (A5) The π–λ Theorem
-- ============================================================
-- Mathematical statement:
-- Let P be a π-system and L be a λ-system.
-- If P ⊆ L, then σ(P) ⊆ L.

theorem pi_lambda (P L : Set (Set Ω)) (hP : IsPiSys P) (hL : IsLambdaSys L)
    (hPL : P ⊆ L) : sigmaGen P ⊆ L := by

  have hGenLambda : lambdaGen P ⊆ L := by
    intro A hA
      -- select arbitrary set from L(P)
      -- A ∈ L
    unfold lambdaGen at hA
      -- A is in intersection of all lambda-sys containing A
    exact Set.mem_sInter.mp hA L ⟨hL, hPL⟩
      -- L is a lambda-sys containing P, so contains lambdaGen P,
      -- which contains A
      -- so A is in L

  have hGenPi : IsPiSys (lambdaGen P) := by
    exact lambdaGen_inter P hP
    -- by main lemma 3, lambdaGen P is closed on intersection,
    -- so its a pi-sys

  have hGenSigma : IsSigmaField (lambdaGen P) := by
    exact isSigmaField_of_lambda_pi
      (lambdaGen P) (lambdaGen_isLambdaSys P) hGenPi
      -- lambda-sys thats closed on intersections is a sigma-field,
      -- so lambdaGen P is a sigma field

  have hSigmaSubset : sigmaGen P ⊆ lambdaGen P := by
    intro A hA
      -- select arbitrary set A from sigmaGen P
      -- R: A ∈ lambdaGen A
    unfold sigmaGen at hA
      -- A in all sigma fields containing P
    exact Set.mem_sInter.mp hA (lambdaGen P)
      ⟨hGenSigma, subset_lambdaGen P⟩
      -- lambdaGen P is a sigma field containing P,
      -- so A ∈ lambdaGen A

  exact Set.Subset.trans hSigmaSubset hGenLambda
    -- sigmaGen P ⊆ lambdaGen P ⊆ L, so
    -- sigmaGen P ⊆ L
    -- 끝
    -- QED
end Math7800.Midterm

#print axioms Math7800.Midterm.lambdaGen_isLambdaSys
#print axioms Math7800.Midterm.subset_lambdaGen
#print axioms Math7800.Midterm.lambdaGen_inter
#print axioms Math7800.Midterm.isSigmaField_of_lambda_pi
#print axioms Math7800.Midterm.pi_lambda
