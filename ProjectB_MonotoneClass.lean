/-
  Math 7800 (Fall 2026) -- Take-home Lean midterm, Project B.
  Scaffold release: 2026-10-13. Due: Thursday, 2026-10-29, Gradescope.

  Read Midterm/README.md before starting.
  Replace ALL five `sorry` placeholders with proofs (four lemmas and
  the main theorem). None may remain in a final submission.
  Keep the definitions, namespace, and five statements unchanged.
  Add helper lemmas as needed. General Mathlib set algebra is allowed.
  Check the two projects separately: they share the frozen definitions.
-/
import Mathlib

open Set Function

namespace Math7800.Midterm

variable {Ω : Type*}

-- BEGIN FROZEN DEFINITIONS
/-- π-system: closed under finite intersection. (∅ allowed, as in Mathlib.) -/
def IsPiSys (P : Set (Set Ω)) : Prop :=
  ∀ A ∈ P, ∀ B ∈ P, A ∩ B ∈ P

/-- λ-system (Billingsley): contains Ω, closed under complements and
countable disjoint unions. -/
structure IsLambdaSys (L : Set (Set Ω)) : Prop where
  univ_mem : univ ∈ L
  compl_mem : ∀ A ∈ L, Aᶜ ∈ L
  iUnion_mem : ∀ f : ℕ → Set Ω, Pairwise (Disjoint on f) → (∀ n, f n ∈ L) →
    (⋃ n, f n) ∈ L

structure IsSigmaField (F : Set (Set Ω)) : Prop where
  univ_mem : univ ∈ F
  compl_mem : ∀ A ∈ F, Aᶜ ∈ F
  iUnion_mem : ∀ f : ℕ → Set Ω, (∀ n, f n ∈ F) → (⋃ n, f n) ∈ F

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

def sigmaGen (A : Set (Set Ω)) : Set (Set Ω) := ⋂₀ {F | IsSigmaField F ∧ A ⊆ F}
def lambdaGen (A : Set (Set Ω)) : Set (Set Ω) := ⋂₀ {L | IsLambdaSys L ∧ A ⊆ L}
def monoGen (A : Set (Set Ω)) : Set (Set Ω) :=
  ⋂₀ {M | IsMonotoneClass M ∧ A ⊆ M}
-- END FROZEN DEFINITIONS


-- ============================================================
-- LEMMA 1: The Generated Monotone Class Is a Monotone Class
-- ============================================================
-- Mathematical statement:
-- Let A be a collection of subsets of Ω.
-- Then monoGen A is a monotone class.
--
-- Mathematically:
-- IsMonotoneClass (monoGen A).
--
-- Proof idea:
-- 1. Recall that monoGen A is the intersection
--    of all monotone classes containing A.
-- 2. Prove closure under increasing countable unions.
-- 3. Prove closure under decreasing countable intersections.
-- 4. Conclude that monoGen A is a monotone class.
--
-- Main principle:
-- The intersection of monotone classes is itself a monotone class.

lemma monoGen_isMonotoneClass (A : Set (Set Ω)) :
    IsMonotoneClass (monoGen A) := by
  -- (monoGen A) mean we apply the definition of monoGen to A first,
  -- then we apply the definition of IsMonotoneClass to the result.

  constructor
  -- Construct the IsMonotoneClass structure.
  -- Lean creates two goals:
  --
  -- Goal 1: Closure under increasing unions.
  -- Goal 2: Closure under decreasing intersections.


  -- ----------------------------------------------------------
  -- PROPERTY 1: Closure Under Increasing Unions
  -- ----------------------------------------------------------
  -- Mathematical statement:
  -- Suppose f(n) ∈ monoGen A for every n,
  -- and the sequence f is increasing.
  --
  -- Then ⋃ n, f(n) ∈ monoGen A.
  --
  -- Proof idea:
  -- Every monotone class containing A is closed
  -- under increasing unions.
  --
  -- Therefore the union belongs to every
  -- such monotone class, hence their intersection.

  intro f hf_mono hf_mem
  -- Introduce the sequence and its hypotheses.
  --
  -- f : ℕ → Set Ω
  -- hf_mono : Monotone f
  -- hf_mem : ∀ n, f n ∈ monoGen A
  --
  -- Monotone f means:
  -- If i ≤ j, then f(i) ⊆ f(j).
  --
  -- Goal: (⋃ n, f n) ∈ monoGen A.

  change (⋃ n, f n) ∈
      ⋂₀ {M : Set (Set Ω) |
        IsMonotoneClass M ∧ A ⊆ M}
  -- Expand the definition of monoGen A.
  --
  -- monoGen A is the intersection of all monotone classes M containing A.
  --
  -- Goal:
  -- The increasing union belongs to this intersection.

  rw [Set.mem_sInter]
  -- Rewrite intersection membership.
  -- ∀ M ∈ S, E ∈ M
  --
  -- New goal:
  -- For every eligible monotone class M,
  -- (⋃ n, f n) ∈ M.

  intro M hM
  -- Introduce an arbitrary eligible collection M.
  --
  -- M : Set (Set Ω)
  -- hM : M belongs to the family of
  --      monotone classes containing A.
  --
  -- Goal: (⋃ n, f n) ∈ M.

  rcases hM with ⟨hMonotone, hAM⟩
  -- Extract the two eligibility conditions.
  --
  -- hMonotone : IsMonotoneClass M
  -- hAM       : A ⊆ M
  --
  -- Goal: (⋃ n, f n) ∈ M.

  have hf_mem_M : ∀ n, f n ∈ M := by
    -- Establish membership of every f(n) in M.
    --
    -- hf_mem proves f(n) ∈ monoGen A.
    -- Since monoGen A is an intersection,
    -- every f(n) belongs to every eligible M.

    intro n
    -- Fix an arbitrary natural number n.
    -- Goal: f n ∈ M.

    exact (Set.mem_sInter.mp (hf_mem n))
        M ⟨hMonotone, hAM⟩
    -- fix n hf_mem n proves f(n) ∈ monoGen A.
    --
    -- Set.mem_sInter.mp extracts membership
    -- in every eligible monotone class.
    --
    -- M selects the particular monotone class.
    -- ⟨hMonotone, hAM⟩ proves eligibility.
    --
    -- Therefore f(n) ∈ M for every n.

  exact hMonotone.iUnion_mem f hf_mono hf_mem_M
  -- Apply increasing-union closure of M.
  -- use hMonotone.iUnion_mem to prove the union belongs to M.
  --
  -- f        : the sequence of sets.
  -- hf_mono  : proves f is increasing.
  -- hf_mem_M : proves every f(n) belongs to M.
  --
  -- Therefore ⋃ n, f(n) ∈ M.
  --
  -- Since M was arbitrary, the union belongs
  -- to every monotone class containing A.
  --
  -- Hence ⋃ n, f(n) ∈ monoGen A.
  -- Property 1 is proved.


  -- ----------------------------------------------------------
  -- PROPERTY 2: Closure Under Decreasing Intersections
  -- ----------------------------------------------------------
  -- Mathematical statement:
  -- Suppose f(n) ∈ monoGen A for every n,
  -- and f is decreasing.
  --
  -- Then ⋂ n, f(n) ∈ monoGen A.
  --
  -- Antitone f means:
  -- If i ≤ j, then f(j) ⊆ f(i).

  intro f hf_anti hf_mem
  -- Introduce an arbitrary decreasing sequence.
  --
  -- f : ℕ → Set Ω
  -- hf_anti : Antitone f
  -- hf_mem  : ∀ n, f n ∈ monoGen A
  --
  -- Goal: (⋂ n, f n) ∈ monoGen A.

  change (⋂ n, f n) ∈
      ⋂₀ {M : Set (Set Ω) |
    IsMonotoneClass M ∧ A ⊆ M}
  -- Expand the definition of monoGen A.
  --
  -- We need to show that the intersection
  -- of the decreasing sequence belongs to
  -- every monotone class containing A.

  rw [Set.mem_sInter]
  -- Rewrite membership in the intersection
  -- as a universal statement over eligible M.

  intro M hM
  -- Choose an arbitrary monotone class M
  -- containing A.
  --
  -- Goal: (⋂ n, f n) ∈ M.

  rcases hM with ⟨hMonotone, hAM⟩
  -- Extract the two eligibility conditions.
  --
  -- hMonotone : IsMonotoneClass M
  -- hAM       : A ⊆ M

  have hf_mem_M : ∀ n, f n ∈ M := by
    -- Transfer membership from monoGen A to M.

    intro n
    -- Fix an arbitrary n.
    -- Goal: f n ∈ M.

    exact (Set.mem_sInter.mp (hf_mem n))
        M ⟨hMonotone, hAM⟩
    -- Since f(n) belongs to monoGen A,
    -- it belongs to every eligible M.
    --
    -- Hence f(n) ∈ M.

  exact hMonotone.iInter_mem f hf_anti hf_mem_M
  -- Apply decreasing-intersection closure of M.
  --
  -- hf_anti proves the sequence is decreasing.
  -- hf_mem_M proves every f(n) belongs to M.
  --
  -- Therefore ⋂ n, f(n) ∈ M.
  --
  -- Since M was arbitrary:
  -- ⋂ n, f(n) ∈ monoGen A.
  --
  -- Property 2 is proved.
  -- Thus monoGen A is a monotone class.
  -- Lemma 1 is complete.


-- ============================================================
-- LEMMA 2: Every σ-Field Is a Monotone Class
-- ============================================================
-- Mathematical statement:
-- If F is a σ-field, then F is a monotone class.
--
-- Mathematically:
-- IsSigmaField F → IsMonotoneClass F.
--
-- Proof idea:
-- 1. A σ-field is closed under arbitrary
--    countable unions, so it is closed
--    under increasing unions.
-- 2. To prove decreasing-intersection closure,
--    use complements and De Morgan's law.
-- 3. Every complement f(n)ᶜ belongs to F.
-- 4. Their countable union belongs to F.
-- 5. The complement of this union belongs to F.
-- 6. By De Morgan's law, this is ⋂ n, f(n).
--
-- Important:
-- We do not actually need the monotonicity
-- assumptions to establish the two properties,
-- because σ-fields are closed under arbitrary
-- countable unions and intersections.

lemma monotone_class_of_sigmaField
    (F : Set (Set Ω)) (hF : IsSigmaField F) :
    IsMonotoneClass F := by

  constructor
  -- Prove the two properties of a monotone class.


  -- ----------------------------------------------------------
  -- PROPERTY 1: Closure Under Increasing Unions
  -- ----------------------------------------------------------

  intro f hf_mono hf_mem
  -- f : ℕ → Set Ω
  -- hf_mono : Monotone f
  -- hf_mem  : ∀ n, f n ∈ F
  --
  -- Goal: (⋃ n, f n) ∈ F.

  exact hF.iUnion_mem f hf_mem
  -- Since F is a σ-field, it is closed under
  -- all countable unions.
  --
  -- Therefore ⋃ n, f(n) ∈ F.
  --
  -- Note:
  -- hf_mono is not needed because σ-field
  -- closure does not require an increasing sequence.


  -- ----------------------------------------------------------
  -- PROPERTY 2: Closure Under Decreasing Intersections
  -- ----------------------------------------------------------

  intro f hf_anti hf_mem
  -- f : ℕ → Set Ω
  -- hf_anti : Antitone f
  -- hf_mem  : ∀ n, f n ∈ F
  --
  -- Goal: (⋂ n, f n) ∈ F.

  have hComp_mem : ∀ n, (f n)ᶜ ∈ F := by
    -- Prove each complement belongs to F.

    intro n
    -- Fix arbitrary n.
    -- Goal: (f n)ᶜ ∈ F.

    exact hF.compl_mem (f n) (hf_mem n)
    -- hf_mem n gives f(n) ∈ F.
    -- Complement closure gives f(n)ᶜ ∈ F.

  have hUnion :
      (⋃ n, (f n)ᶜ) ∈ F := by
    -- Apply countable union closure to complements.

    exact hF.iUnion_mem
      (fun n => (f n)ᶜ) hComp_mem
    -- Every f(n)ᶜ belongs to F.
    --
    -- Therefore ⋃ n, f(n)ᶜ ∈ F.

  have hCompUnion :
      (⋃ n, (f n)ᶜ)ᶜ ∈ F := by
    -- Take the complement of the countable union.

    exact hF.compl_mem
      (⋃ n, (f n)ᶜ) hUnion
    -- Since the union belongs to F,
    -- its complement also belongs to F.

  simpa only [Set.compl_iUnion, compl_compl]
    using hCompUnion
  -- Use De Morgan's law:
  --
  -- (⋃ n, f(n)ᶜ)ᶜ
  --   = ⋂ n, (f(n)ᶜ)ᶜ
  --   = ⋂ n, f(n).
  --
  -- Set.compl_iUnion rewrites the complement
  -- of a union as an intersection of complements.
  --
  -- compl_compl removes double complements.
  --
  -- Therefore ⋂ n, f(n) ∈ F.
  -- Lemma 2 is proved.


-- ============================================================
-- HELPER 1: Inclusion of the Generating Collection
-- ============================================================
-- Mathematical statement:
-- Let A be a collection of subsets of Ω.
-- Then A ⊆ monoGen A.
--
-- Equivalently:
-- For every E ∈ A, E ∈ monoGen A.
--
-- Proof idea:
-- 1. Choose an arbitrary E ∈ A.
-- 2. Expand monoGen A as the intersection
--    of all monotone classes containing A.
-- 3. Choose an arbitrary eligible monotone class M.
-- 4. Since A ⊆ M and E ∈ A, we obtain E ∈ M.
-- 5. Therefore E belongs to every eligible M.
-- 6. Conclude E ∈ monoGen A.

private lemma subset_monoGen (A : Set (Set Ω)) :
    A ⊆ monoGen A := by

  intro E hE
  -- Introduce arbitrary E ∈ A.
  --
  -- E : Set Ω
  -- hE : E ∈ A
  --
  -- Goal: E ∈ monoGen A.

  change E ∈ ⋂₀ {M : Set (Set Ω) |
    IsMonotoneClass M ∧ A ⊆ M}
  -- Expand the definition of monoGen A.
  --
  -- Goal:
  -- E belongs to the intersection of all
  -- monotone classes containing A.

  rw [Set.mem_sInter]
  -- To prove membership in an intersection,
  -- prove membership in every eligible collection.

  intro M hM
  -- Choose an arbitrary monotone class M
  -- containing A.
  --
  -- Goal: E ∈ M.

  exact hM.2 hE
  -- hM is a conjunction:
  -- IsMonotoneClass M ∧ A ⊆ M.
  --
  -- hM.2 extracts the second condition:
  -- A ⊆ M.
  --
  -- hE proves E ∈ A.
  --
  -- Therefore E ∈ M.
  --
  -- Since M was arbitrary, E ∈ monoGen A.
  -- Helper 1 is proved.


-- ============================================================
-- HELPER 2: Minimality of the Generated Monotone Class
-- ============================================================
-- Mathematical statement:
-- Suppose M is a monotone class containing A.
-- Then monoGen A ⊆ M.
--
-- Proof idea:
-- 1. Choose an arbitrary E ∈ monoGen A.
-- 2. Since monoGen A is the intersection
--    of all monotone classes containing A,
--    E belongs to every such monotone class.
-- 3. Since M is a monotone class containing A,
--    M is one of the eligible collections.
-- 4. Therefore E ∈ M.
-- 5. Conclude monoGen A ⊆ M.
--
-- This is the minimality property used
-- repeatedly in the Monotone Class Theorem.

private lemma monoGen_minimal
    (A M : Set (Set Ω))
    (hM : IsMonotoneClass M)
    (hAM : A ⊆ M) :
    monoGen A ⊆ M := by

  intro E hE
  -- Introduce arbitrary E ∈ monoGen A.
  --
  -- hE : E ∈ monoGen A
  -- Goal: E ∈ M.

  exact (Set.mem_sInter.mp hE) M ⟨hM, hAM⟩
  -- Set.mem_sInter.mp hE proves E belongs
  -- to every monotone class containing A.
  --
  -- M specifies the particular collection.
  --
  -- ⟨hM, hAM⟩ verifies eligibility:
  -- hM  : M is a monotone class.
  -- hAM : A ⊆ M.
  --
  -- Therefore E ∈ M.
  --
  -- Since E was arbitrary:
  -- monoGen A ⊆ M.
  -- Helper 2 is proved.


-- ============================================================
-- HELPER 3: The Union Good-Set Construction
-- ============================================================
-- Mathematical statement:
-- Let M be a monotone class and fix C ⊆ Ω.
-- Define
--
-- D = {E | E ∈ M ∧ C ∪ E ∈ M}.
--
-- Then D is a monotone class.
--
-- Note:
-- We do NOT assume C ∈ M in this helper.
--
-- Proof idea:
-- 1. Take an increasing sequence f(n) in D.
-- 2. Since f(n) ∈ D, both f(n) and C ∪ f(n)
--    belong to M.
-- 3. Show C ∪ f(n) is increasing.
-- 4. Apply increasing-union closure of M.
-- 5. Use distributivity of union over indexed unions.
-- 6. Repeat for a decreasing sequence,
--    using intersection closure and
--    distributivity of union over indexed intersections.
-- 7. Conclude D is a monotone class.

private lemma union_good_isMonotoneClass
    (M : Set (Set Ω))
    (hM : IsMonotoneClass M)
    (C : Set Ω) :
    IsMonotoneClass
      {E | E ∈ M ∧ C ∪ E ∈ M} := by

  constructor
  -- We must prove two closure properties:
  -- increasing unions and decreasing intersections.


  -- ----------------------------------------------------------
  -- PROPERTY 1: Increasing Union Closure
  -- ----------------------------------------------------------

  intro f hf_mono hf_mem
  -- f : ℕ → Set Ω
  -- hf_mono : Monotone f
  -- hf_mem : ∀ n, f n ∈ D
  --
  -- Goal: (⋃ n, f n) ∈ D.
  --
  -- By the definition of D, we must show:
  -- 1. (⋃ n, f n) ∈ M.
  -- 2. C ∪ (⋃ n, f n) ∈ M.

  have hfM : ∀ n, f n ∈ M := by
    intro n
    -- Fix arbitrary n.
    -- Goal: f n ∈ M.

    exact (hf_mem n).1
    -- hf_mem n states:
    -- f(n) ∈ M ∧ C ∪ f(n) ∈ M.
    --
    -- .1 extracts the first part.

  have hfUnion : ∀ n, C ∪ f n ∈ M := by
    intro n
    -- Goal: C ∪ f n ∈ M.

    exact (hf_mem n).2
    -- .2 extracts the second part
    -- of membership in the good-set family.

  have hUnionMono : Monotone (fun n => C ∪ f n) := by
    -- Prove the sequence C ∪ f(n) is increasing.
    --
    -- Since f(i) ⊆ f(j) for i ≤ j,
    -- C ∪ f(i) ⊆ C ∪ f(j).

    intro i j hij x hx
    -- hij : i ≤ j.
    -- hx : x ∈ C ∪ f(i).
    -- Goal: x ∈ C ∪ f(j).

    rcases hx with hxC | hxi
    -- Split union membership:
    -- Case 1: x ∈ C.
    -- Case 2: x ∈ f(i).

    exact Or.inl hxC
    -- If x ∈ C, then x ∈ C ∪ f(j).

    exact Or.inr (hf_mono hij hxi)
    -- If x ∈ f(i), monotonicity gives x ∈ f(j).
    -- Therefore x ∈ C ∪ f(j).

  have hFirst : (⋃ n, f n) ∈ M := by
    exact hM.iUnion_mem f hf_mono hfM
    -- f is increasing and every f(n) belongs to M.
    -- Apply increasing-union closure of M.

  have hSecond : (⋃ n, C ∪ f n) ∈ M := by
    exact hM.iUnion_mem
      (fun n => C ∪ f n) hUnionMono hfUnion
    -- The sequence C ∪ f(n) is increasing,
    -- and every term belongs to M.
    --
    -- Therefore its union belongs to M.

  change (⋃ n, f n) ∈ M ∧
    C ∪ (⋃ n, f n) ∈ M
  -- Expand membership in D into two conditions.
  --
  -- Goal 1: The original union belongs to M.
  -- Goal 2: Its union with C belongs to M.

  constructor
  -- Split the conjunction into two goals.

  exact hFirst
  -- Prove the first condition using hFirst.

  simpa only [Set.union_iUnion] using hSecond
  -- Apply the distributive identity:
  --
  -- ⋃ n, (C ∪ f(n)) = C ∪ (⋃ n, f(n)).
  --
  -- hSecond proves the left expression belongs to M.
  -- Rewriting gives the required second condition.


  -- ----------------------------------------------------------
  -- PROPERTY 2: Decreasing Intersection Closure
  -- ----------------------------------------------------------

  intro f hf_anti hf_mem
  -- f : ℕ → Set Ω
  -- hf_anti : Antitone f
  -- hf_mem : ∀ n, f n ∈ D
  --
  -- Goal: (⋂ n, f n) ∈ D.

  have hfM : ∀ n, f n ∈ M := by
    intro n
    exact (hf_mem n).1
    -- Every f(n) belongs to M.

  have hfUnion : ∀ n, C ∪ f n ∈ M := by
    intro n
    exact (hf_mem n).2
    -- Every C ∪ f(n) belongs to M.

  have hUnionAnti : Antitone (fun n => C ∪ f n) := by
    -- Prove the sequence C ∪ f(n) is decreasing.
    --
    -- If i ≤ j, then f(j) ⊆ f(i).
    -- Hence C ∪ f(j) ⊆ C ∪ f(i).

    intro i j hij x hx
    -- hij : i ≤ j.
    -- hx : x ∈ C ∪ f(j).
    -- Goal: x ∈ C ∪ f(i).

    rcases hx with hxC | hxj

    exact Or.inl hxC
    -- If x belongs to C, the conclusion is immediate.

    exact Or.inr (hf_anti hij hxj)
    -- If x belongs to f(j), antitonicity gives
    -- x ∈ f(i).

  have hFirst : (⋂ n, f n) ∈ M := by
    exact hM.iInter_mem f hf_anti hfM
    -- Use decreasing-intersection closure of M.

  have hSecond : (⋂ n, C ∪ f n) ∈ M := by
    exact hM.iInter_mem
      (fun n => C ∪ f n) hUnionAnti hfUnion
    -- Apply decreasing-intersection closure to
    -- the sequence C ∪ f(n).

  change (⋂ n, f n) ∈ M ∧
    C ∪ (⋂ n, f n) ∈ M
  -- Expand membership in D.
  -- We need both parts of the conjunction.

  constructor

  exact hFirst
  -- The decreasing intersection belongs to M.

  simpa only [Set.union_iInter] using hSecond
  -- Use distributivity:
  --
  -- ⋂ n, (C ∪ f(n)) = C ∪ (⋂ n, f(n)).
  --
  -- The set C is fixed for every n.
  --
  -- Hence C ∪ (⋂ n, f(n)) belongs to M.
  --
  -- Both monotone-class properties are proved.
  -- Helper 3 is complete.



-- ============================================================
-- LEMMA 3: The monotone class generated by a field is a field
-- ============================================================
-- Mathematical statement:
-- Let F₀ be a field of subsets of Ω.
-- Then monoGen F₀ is also a field.
--
-- Mathematically:
-- IsField F₀ → IsField (monoGen F₀).
--
-- Proof idea:
-- 1. Let M = monoGen F₀.
-- 2. Establish that M is a monotone class
--    and F₀ ⊆ M.
-- 3. Prove M is closed under complements,
--    using a good-set family and minimality.
-- 4. Prove C ∪ E ∈ M when C ∈ F₀ and E ∈ M.
-- 5. Extend union closure to A, B ∈ M.
-- 6. Prove Ω ∈ M.
-- 7. Assemble the three field properties:
--    universal-set membership, complement closure,
--    and finite union closure.

lemma monoGen_isField
    (F₀ : Set (Set Ω)) (hF₀ : IsField F₀) :
    IsField (monoGen F₀) := by

  let M := monoGen F₀
  -- Define M as the monotone class generated by F₀.
  -- This notation makes subsequent statements shorter.

  have hM : IsMonotoneClass M :=
    monoGen_isMonotoneClass F₀
  -- USE LEMMA 1.
  -- M is a monotone class.

  have hFsub : F₀ ⊆ M :=
    subset_monoGen F₀
  -- USE HELPER 1.
  -- The original field F₀ is contained in M.


  -- ----------------------------------------------------------
  -- STAGE 1: Prove Complement Closure of M
  -- ----------------------------------------------------------
  -- Goal:
  -- ∀ E ∈ M, Eᶜ ∈ M.
  --
  -- We define:
  -- D = {E | E ∈ M ∧ Eᶜ ∈ M}.
  --
  -- We will show D is a monotone class
  -- containing F₀, then apply minimality.

  have hCompl : ∀ E ∈ M, Eᶜ ∈ M := by

    let D : Set (Set Ω) :=
      {E | E ∈ M ∧ Eᶜ ∈ M}
    -- D consists of sets E such that
    -- both E and its complement belong to M.

    have hD : IsMonotoneClass D := by
      constructor
      -- Prove D is closed under:
      -- 1. Increasing unions.
      -- 2. Decreasing intersections.


      -- ------------------------------------------------------
      -- PART A: Increasing Unions in D
      -- ------------------------------------------------------

      · intro f hf_mono hf_mem
        -- f is an increasing sequence in D.
        --
        -- hf_mono : Monotone f
        -- hf_mem : ∀ n, f n ∈ D
        --
        -- Goal: ⋃ n, f(n) ∈ D.

        have hfM : ∀ n, f n ∈ M := by
          intro n
          exact (hf_mem n).1
          -- Since f(n) ∈ D, f(n) ∈ M.

        have hfComp : ∀ n, (f n)ᶜ ∈ M := by
          intro n
          exact (hf_mem n).2
          -- Since f(n) ∈ D, its complement
          -- also belongs to M.

        have hfCompAnti :
            Antitone (fun n => (f n)ᶜ) := by
          -- Complements reverse set inclusion.
          --
          -- Since f is increasing,
          -- the complement sequence is decreasing.

          intro i j hij x hx hxfi
          -- hij : i ≤ j.
          -- hx : x ∈ f(j)ᶜ.
          -- hxfi : x ∈ f(i).
          --
          -- Goal: False.

          exact hx (hf_mono hij hxfi)
          -- From x ∈ f(i), monotonicity gives
          -- x ∈ f(j).
          --
          -- But hx says x ∉ f(j).
          -- Contradiction.

        have hUnion : (⋃ n, f n) ∈ M :=
          hM.iUnion_mem f hf_mono hfM
        -- Apply increasing-union closure of M.

        have hInterComp :
            (⋂ n, (f n)ᶜ) ∈ M :=
          hM.iInter_mem
            (fun n => (f n)ᶜ)
            hfCompAnti hfComp
        -- The complement sequence is decreasing,
        -- and every complement belongs to M.
        --
        -- Therefore their intersection belongs to M.

        change (⋃ n, f n) ∈ M ∧
          (⋃ n, f n)ᶜ ∈ M
        -- Expand membership in D.
        --
        -- We must prove the union belongs to M
        -- and its complement belongs to M.

        constructor

        · exact hUnion
          -- First condition is established.

        · simpa only [Set.compl_iUnion] using hInterComp
          -- De Morgan's law:
          --
          -- (⋃ n, f(n))ᶜ = ⋂ n, f(n)ᶜ.
          --
          -- hInterComp proves the right side
          -- belongs to M.
          --
          -- Hence the complement of the union
          -- also belongs to M.


      -- ------------------------------------------------------
      -- PART B: Decreasing Intersections in D
      -- ------------------------------------------------------

      · intro f hf_anti hf_mem
        -- f is a decreasing sequence in D.
        --
        -- hf_anti : Antitone f
        -- hf_mem : ∀ n, f n ∈ D
        --
        -- Goal: ⋂ n, f(n) ∈ D.

        have hfM : ∀ n, f n ∈ M := by
          intro n
          exact (hf_mem n).1
          -- Every f(n) belongs to M.

        have hfComp : ∀ n, (f n)ᶜ ∈ M := by
          intro n
          exact (hf_mem n).2
          -- Every complement belongs to M.

        have hfCompMono :
            Monotone (fun n => (f n)ᶜ) := by
          -- Since f is decreasing,
          -- its complement sequence is increasing.

          intro i j hij x hx hxfi
          -- hx : x ∈ f(i)ᶜ.
          -- hxfi : x ∈ f(j).
          -- Goal: False.

          exact hx (hf_anti hij hxfi)
          -- Antitonicity gives x ∈ f(i).
          -- But hx says x ∉ f(i).
          -- Contradiction.

        have hInter : (⋂ n, f n) ∈ M :=
          hM.iInter_mem f hf_anti hfM
        -- Apply decreasing-intersection closure of M.

        have hUnionComp :
            (⋃ n, (f n)ᶜ) ∈ M :=
          hM.iUnion_mem
            (fun n => (f n)ᶜ)
            hfCompMono hfComp
        -- The complement sequence is increasing.
        -- Hence its union belongs to M.

        change (⋂ n, f n) ∈ M ∧
          (⋂ n, f n)ᶜ ∈ M
        -- Expand membership in D.

        constructor

        · exact hInter
          -- The intersection belongs to M.

        · simpa only [Set.compl_iInter] using hUnionComp
          -- De Morgan's law:
          --
          -- (⋂ n, f(n))ᶜ = ⋃ n, f(n)ᶜ.
          --
          -- hUnionComp establishes membership of
          -- the right side in M.
          --
          -- Hence the complement of the intersection
          -- also belongs to M.

    -- D is now known to be a monotone class.


    -- --------------------------------------------------------
    -- Show F₀ is contained in D.
    -- --------------------------------------------------------

    have hFsubD : F₀ ⊆ D := by
      intro E hE
      -- Choose arbitrary E ∈ F₀.
      -- Goal: E ∈ D.

      change E ∈ M ∧ Eᶜ ∈ M
      -- Expand D membership into two conditions.

      constructor

      · exact hFsub hE
        -- Since F₀ ⊆ M, E ∈ M.

      · exact hFsub (hF₀.compl_mem E hE)
        -- F₀ is a field, so Eᶜ ∈ F₀.
        -- Since F₀ ⊆ M, Eᶜ ∈ M.

    intro E hE
    -- Choose arbitrary E ∈ M.
    -- Goal: Eᶜ ∈ M.

    have hED : E ∈ D :=
      monoGen_minimal F₀ D hD hFsubD hE
    -- USE HELPER 2: monoGen_minimal.
    --
    -- D is a monotone class containing F₀.
    -- Therefore M = monoGen F₀ ⊆ D.
    --
    -- Since E ∈ M, we get E ∈ D.

    exact hED.2
    -- E ∈ D means E ∈ M ∧ Eᶜ ∈ M.
    -- .2 extracts Eᶜ ∈ M.
    --
    -- Complement closure of M is proved.


  -- ----------------------------------------------------------
  -- STAGE 2: One Set in F₀, One Set in M
  -- ----------------------------------------------------------
  -- Goal:
  -- If C ∈ F₀ and E ∈ M, then C ∪ E ∈ M.
  --
  -- This is an intermediate union closure result.

  have hStage1 :
      ∀ C ∈ F₀, ∀ E ∈ M, C ∪ E ∈ M := by

    intro C hC
    -- Fix arbitrary C ∈ F₀.
    --
    -- Goal: ∀ E ∈ M, C ∪ E ∈ M.

    let D : Set (Set Ω) :=
      {E | E ∈ M ∧ C ∪ E ∈ M}
    -- Define the union good-set family.
    --
    -- D consists of E such that:
    -- 1. E ∈ M.
    -- 2. C ∪ E ∈ M.

    have hD : IsMonotoneClass D :=
      union_good_isMonotoneClass M hM C
    -- USE HELPER 3.
    -- The good-set family D is a monotone class.

    have hFD : F₀ ⊆ D := by
      -- Show that D contains every generator.

      intro E hE
      -- Choose E ∈ F₀.

      change E ∈ M ∧ C ∪ E ∈ M
      -- Expand D membership.

      constructor

      · exact hFsub hE
        -- Since F₀ ⊆ M, E ∈ M.

      · exact hFsub (hF₀.union_mem C hC E hE)
        -- Since C, E ∈ F₀ and F₀ is a field,
        -- C ∪ E ∈ F₀.
        --
        -- By F₀ ⊆ M, C ∪ E ∈ M.

    intro E hE
    -- Choose arbitrary E ∈ M.
    -- Goal: C ∪ E ∈ M.

    have hED : E ∈ D :=
      monoGen_minimal F₀ D hD hFD hE
    -- USE HELPER 2.
    --
    -- Since D is a monotone class containing F₀,
    -- minimality gives M ⊆ D.
    --
    -- Thus E ∈ D.

    exact hED.2
    -- E ∈ D implies C ∪ E ∈ M.
    --
    -- This completes union closure when
    -- the first set belongs to F₀.


  -- ----------------------------------------------------------
  -- STAGE 3: Both Sets Belong to M
  -- ----------------------------------------------------------
  -- Goal:
  -- ∀ A, B ∈ M, A ∪ B ∈ M.
  --
  -- We use Stage 2 to extend union closure
  -- from generators to arbitrary elements of M.

  have hUnion :
      ∀ A ∈ M, ∀ B ∈ M, A ∪ B ∈ M := by

    intro A hA B hB
    -- Choose arbitrary A, B ∈ M.
    -- Goal: A ∪ B ∈ M.

    let D : Set (Set Ω) :=
      {E | E ∈ M ∧ B ∪ E ∈ M}
    -- Fix B and construct:
    --
    -- D = {E ∈ M | B ∪ E ∈ M}.
    --
    -- We will prove M ⊆ D.

    have hD : IsMonotoneClass D :=
      union_good_isMonotoneClass M hM B
    -- USE HELPER 3 AGAIN.
    --
    -- D is a monotone class.

    have hFD : F₀ ⊆ D := by
      intro E hE
      -- Choose arbitrary E ∈ F₀.
      -- Goal: E ∈ D.

      change E ∈ M ∧ B ∪ E ∈ M
      -- Expand membership in D.

      constructor

      · exact hFsub hE
        -- E ∈ F₀ and F₀ ⊆ M imply E ∈ M.

      · have hEB : E ∪ B ∈ M :=
          hStage1 E hE B hB
        -- USE STAGE 2: hStage1.
        --
        -- E ∈ F₀ and B ∈ M.
        -- Therefore E ∪ B ∈ M.

        simpa only [union_comm] using hEB
        -- Our goal is B ∪ E ∈ M.
        --
        -- Since union is commutative:
        -- E ∪ B = B ∪ E.
        --
        -- simpa transforms hEB into the required result.

    have hAD : A ∈ D :=
      monoGen_minimal F₀ D hD hFD hA
    -- USE HELPER 2.
    --
    -- D is a monotone class containing F₀.
    -- Therefore M ⊆ D.
    --
    -- Since A ∈ M, it follows that A ∈ D.

    simpa only [union_comm] using hAD.2
    -- hAD.2 proves B ∪ A ∈ M.
    --
    -- Our goal is A ∪ B ∈ M.
    -- Union commutativity establishes equality.
    --
    -- Hence arbitrary finite union closure holds.


  -- ----------------------------------------------------------
  -- FINAL STAGE: Construct the IsField Structure
  -- ----------------------------------------------------------
  -- A field requires:
  -- 1. Ω ∈ M.
  -- 2. Complement closure.
  -- 3. Finite union closure.

  constructor
  -- Split the field structure into three goals.

  · exact hFsub hF₀.univ_mem
    -- F₀ is a field, so Ω ∈ F₀.
    -- Since F₀ ⊆ M, Ω ∈ M.

  · intro E hE
    exact hCompl E hE
    -- Apply the complement closure
    -- established in Stage 1.

  · intro A hA B hB
    exact hUnion A hA B hB
    -- Apply union closure
    -- established in Stage 3.
    --
    -- All three field properties are established.
    -- Lemma 3 is proved.


-- ============================================================
-- HELPER 4: The Generated σ-Field Is a σ-Field
-- ============================================================
-- Mathematical statement:
-- Let A be a collection of subsets of Ω.
-- Then sigmaGen A is a σ-field.
--
-- Proof idea:
-- 1. Recall sigmaGen A is the intersection
--    of all σ-fields containing A.
-- 2. Prove Ω belongs to this intersection.
-- 3. Prove complement closure.
-- 4. Prove arbitrary countable union closure.
-- 5. Conclude sigmaGen A is a σ-field.
--
-- This parallels the generated λ-system
-- proof from Project A.

private lemma sigmaGen_isSigmaField
    (A : Set (Set Ω)) :
    IsSigmaField (sigmaGen A) := by

  constructor
  -- Construct the σ-field structure.
  -- Three goals:
  -- univ_mem, compl_mem, iUnion_mem.


  -- ----------------------------------------------------------
  -- PROPERTY 1: Universal Set Membership
  -- ----------------------------------------------------------

  · change (univ : Set Ω) ∈
      ⋂₀ {F : Set (Set Ω) |
        IsSigmaField F ∧ A ⊆ F}
    -- Expand the definition of sigmaGen A.
    --
    -- Goal: Ω belongs to the intersection
    -- of all σ-fields containing A.

    rw [Set.mem_sInter]
    -- Convert intersection membership into
    -- membership in every eligible σ-field.

    intro F hF
    -- Choose an arbitrary eligible F.
    --
    -- hF states:
    -- IsSigmaField F ∧ A ⊆ F.

    exact hF.1.univ_mem
    -- hF.1 proves F is a σ-field.
    -- Every σ-field contains Ω.
    --
    -- Therefore Ω ∈ F.
    -- Since F was arbitrary, Ω ∈ sigmaGen A.


  -- ----------------------------------------------------------
  -- PROPERTY 2: Complement Closure
  -- ----------------------------------------------------------

  · intro E hE
    -- E : Set Ω
    -- hE : E ∈ sigmaGen A
    --
    -- Goal: Eᶜ ∈ sigmaGen A.

    change Eᶜ ∈
        ⋂₀ {F : Set (Set Ω) |
          IsSigmaField F ∧ A ⊆ F}
    -- Expand sigmaGen A.

    rw [Set.mem_sInter]
    -- We must show Eᶜ belongs to every
    -- eligible σ-field F.

    intro F hF
    -- Choose arbitrary F.
    -- hF : IsSigmaField F ∧ A ⊆ F.
    --
    -- Goal: Eᶜ ∈ F.

    have hEF : E ∈ F :=
      (Set.mem_sInter.mp hE) F hF
    -- Since E ∈ sigmaGen A, E belongs to
    -- every σ-field containing A.
    --
    -- Hence E ∈ F.

    exact hF.1.compl_mem E hEF
    -- hF.1 proves F is a σ-field.
    -- hEF proves E ∈ F.
    --
    -- Complement closure gives Eᶜ ∈ F.
    -- Thus Eᶜ ∈ sigmaGen A.


  -- ----------------------------------------------------------
  -- PROPERTY 3: Countable Union Closure
  -- ----------------------------------------------------------

  · intro f hf_mem
    -- f : ℕ → Set Ω
    -- hf_mem : ∀ n, f n ∈ sigmaGen A
    --
    -- Goal: (⋃ n, f n) ∈ sigmaGen A.
    --
    -- No pairwise-disjointness assumption is needed.

    change (⋃ n, f n) ∈
        ⋂₀ {F : Set (Set Ω) |
          IsSigmaField F ∧ A ⊆ F}
    -- Expand sigmaGen A.

    rw [Set.mem_sInter]
    -- Prove the union belongs to every
    -- σ-field F containing A.

    intro F hF
    -- Choose arbitrary eligible F.

    have hfF : ∀ n, f n ∈ F := by
      intro n
      -- Fix arbitrary n.
      -- Goal: f n ∈ F.

      exact (Set.mem_sInter.mp (hf_mem n)) F hF
      -- Since f(n) ∈ sigmaGen A,
      -- it belongs to every eligible F.
      --
      -- Therefore f(n) ∈ F.

    exact hF.1.iUnion_mem f hfF
    -- Apply countable union closure of F.
    --
    -- All f(n) belong to F.
    -- Therefore their union belongs to F.
    --
    -- Since F was arbitrary, the union
    -- belongs to sigmaGen A.
    --
    -- All three σ-field properties are established.
    -- Helper 4 is proved.


-- ============================================================
-- HELPER 5: Inclusion of the Generating Collection
-- ============================================================
-- Mathematical statement:
-- For any collection A of subsets of Ω,
-- A ⊆ sigmaGen A.
--
-- Proof idea:
-- 1. Choose arbitrary E ∈ A.
-- 2. Expand sigmaGen A into the intersection
--    of all σ-fields containing A.
-- 3. Choose any eligible σ-field F.
-- 4. Since A ⊆ F, E ∈ F.
-- 5. Conclude E ∈ sigmaGen A.

private lemma subset_sigmaGen
    (A : Set (Set Ω)) :
    A ⊆ sigmaGen A := by

  intro E hE
  -- E : Set Ω
  -- hE : E ∈ A
  --
  -- Goal: E ∈ sigmaGen A.

  change E ∈ ⋂₀ {F : Set (Set Ω) |
    IsSigmaField F ∧ A ⊆ F}
  -- Expand sigmaGen A.

  rw [Set.mem_sInter]
  -- To prove membership in an intersection,
  -- prove membership in every eligible F.

  intro F hF
  -- Choose arbitrary σ-field F containing A.
  --
  -- hF is a conjunction:
  -- IsSigmaField F ∧ A ⊆ F.

  exact hF.2 hE
  -- hF.2 extracts A ⊆ F.
  -- hE proves E ∈ A.
  --
  -- Thus E ∈ F.
  --
  -- Since F was arbitrary,
  -- E ∈ sigmaGen A.
  --
  -- Therefore A ⊆ sigmaGen A.
  -- Helper 5 is proved.



-- ============================================================
-- LEMMA 4: A Field That Is a Monotone Class Is a σ-Field
-- ============================================================
-- Mathematical statement:
-- Suppose F is a field and a monotone class.
-- Then F is a σ-field.
--
-- Proof idea:
-- 1. The field property gives Ω ∈ F.
-- 2. The field property gives complement closure.
-- 3. For an arbitrary sequence f(n) ∈ F,
--    construct increasing finite unions:
--    g(n) = f(0) ∪ ... ∪ f(n).
-- 4. Prove every g(n) belongs to F by induction.
-- 5. Prove g is increasing.
-- 6. Apply monotone-class increasing union closure.
-- 7. Since ⋃ g(n) = ⋃ f(n), conclude arbitrary
--    countable union closure.
-- 8. Therefore F is a σ-field.

lemma isSigmaField_of_field_monotone
    (F : Set (Set Ω))
    (hF : IsField F)
    (hM : IsMonotoneClass F) :
    IsSigmaField F := by

  constructor
  -- Prove the three σ-field properties.


  -- ----------------------------------------------------------
  -- PROPERTY 1: Universal Set Membership
  -- ----------------------------------------------------------

  · exact hF.univ_mem
    -- Since F is a field, Ω ∈ F.


  -- ----------------------------------------------------------
  -- PROPERTY 2: Complement Closure
  -- ----------------------------------------------------------

  · intro A hA
    -- Choose arbitrary A ∈ F.
    -- Goal: Aᶜ ∈ F.

    exact hF.compl_mem A hA
    -- Apply complement closure of the field.


  -- ----------------------------------------------------------
  -- PROPERTY 3: Arbitrary Countable Union Closure
  -- ----------------------------------------------------------

  · intro f hf_mem
    -- f : ℕ → Set Ω
    -- hf_mem : ∀ n, f n ∈ F
    --
    -- Goal: (⋃ n, f n) ∈ F.
    --
    -- The original sequence is not necessarily increasing.
    -- We construct an increasing sequence instead.

    -- --------------------------------------------------------
    -- STEP 1: Define Increasing Finite Unions
    -- --------------------------------------------------------

    let g : ℕ → Set Ω := Set.accumulate f
    -- Define g using Mathlib's Set.accumulate.
    --
    -- g(0) = f(0).
    -- g(n+1) = g(n) ∪ f(n+1).
    --
    -- Thus:
    -- g(n) = ⋃_{k≤n} f(k).
    --
    -- The sequence g is increasing.


    -- --------------------------------------------------------
    -- STEP 2: Show Each g(n) Belongs to F
    -- --------------------------------------------------------

    have hg_mem : ∀ n, g n ∈ F := by
      intro n
      -- Fix arbitrary n.
      -- Goal: g(n) ∈ F.

      induction n with
      -- Prove the statement by induction on n.

      | zero =>
          simpa [g] using (hf_mem 0)
          -- Base case: g(0) = f(0).
          --
          -- hf_mem 0 proves f(0) ∈ F.
          -- Therefore g(0) ∈ F.

      | succ n ih =>
          -- Induction hypothesis:
          -- ih : g(n) ∈ F.
          --
          -- Goal: g(n+1) ∈ F.

          change Set.accumulate f (n + 1) ∈ F
          -- Expand the local definition g.

          rw [Set.accumulate_succ]
          -- Rewrite:
          -- g(n+1) = g(n) ∪ f(n+1).

          exact hF.union_mem
            (Set.accumulate f n) ih
            (f (n + 1)) (hf_mem (n + 1))
          -- Apply finite union closure of F.
          --
          -- ih proves g(n) ∈ F.
          -- hf_mem (n+1) proves f(n+1) ∈ F.
          --
          -- Therefore g(n+1) ∈ F.


    -- --------------------------------------------------------
    -- STEP 3: Prove g Is Increasing
    -- --------------------------------------------------------

    have hg_mono : Monotone g := by
      exact Set.monotone_accumulate
      -- Mathlib provides this theorem.
      --
      -- Since g(n) accumulates more sets as n grows,
      -- g(i) ⊆ g(j) whenever i ≤ j.


    -- --------------------------------------------------------
    -- STEP 4: Apply Monotone-Class Closure
    -- --------------------------------------------------------

    have hg_union : (⋃ n, g n) ∈ F := by
      exact hM.iUnion_mem g hg_mono hg_mem
      -- g is increasing, by hg_mono.
      -- Every g(n) belongs to F, by hg_mem.
      --
      -- Since F is a monotone class,
      -- ⋃ n, g(n) ∈ F.


    -- --------------------------------------------------------
    -- STEP 5: Identify the Accumulated Union
    -- --------------------------------------------------------

    change (⋃ n, Set.accumulate f n) ∈ F at hg_union
    -- Expand the local definition of g
    -- in the hypothesis hg_union.

    rw [Set.iUnion_accumulate] at hg_union
    -- Mathlib proves:
    --
    -- ⋃ n, Set.accumulate f n = ⋃ n, f n.
    --
    -- Rewrite hg_union using this equality.

    exact hg_union
    -- hg_union now proves:
    -- (⋃ n, f n) ∈ F.
    --
    -- All σ-field properties are established.
    -- Lemma 4 is proved.



-- ============================================================
-- FINAL THEOREM: The Monotone Class Theorem
-- ============================================================
-- Mathematical statement:
-- Let F₀ be a field of subsets of Ω.
-- Then the monotone class generated by F₀
-- equals the σ-field generated by F₀.
--
-- Mathematically:
-- monoGen F₀ = sigmaGen F₀.
--
-- Proof idea:
-- Prove equality by showing two inclusions.
--
-- Direction 1:
-- monoGen F₀ ⊆ sigmaGen F₀.
--
-- 1. sigmaGen F₀ is a σ-field.
-- 2. Every σ-field is a monotone class.
-- 3. sigmaGen F₀ contains F₀.
-- 4. Minimality of monoGen gives the inclusion.
--
-- Direction 2:
-- sigmaGen F₀ ⊆ monoGen F₀.
--
-- 1. monoGen F₀ is a field, by Lemma 3.
-- 2. monoGen F₀ is a monotone class, by Lemma 1.
-- 3. A field that is a monotone class is a σ-field.
-- 4. monoGen F₀ contains F₀.
-- 5. Minimality of sigmaGen gives the inclusion.
--
-- Combining both inclusions proves equality.

theorem monotone_class
    (F₀ : Set (Set Ω))
    (hF₀ : IsField F₀) :
    monoGen F₀ = sigmaGen F₀ := by

  apply Set.Subset.antisymm
  -- Prove set equality using mutual inclusion.
  --
  -- Goal 1: monoGen F₀ ⊆ sigmaGen F₀.
  -- Goal 2: sigmaGen F₀ ⊆ monoGen F₀.


  -- ----------------------------------------------------------
  -- DIRECTION 1: monoGen F₀ ⊆ sigmaGen F₀
  -- ----------------------------------------------------------

  · have hSigma :
        IsSigmaField (sigmaGen F₀) :=
      sigmaGen_isSigmaField F₀
    -- USE HELPER 4.
    --
    -- The generated σ-field sigmaGen F₀
    -- is itself a σ-field.

    have hMonotone :
        IsMonotoneClass (sigmaGen F₀) :=
      monotone_class_of_sigmaField
        (sigmaGen F₀) hSigma
    -- USE LEMMA 2.
    --
    -- Every σ-field is a monotone class.
    -- Therefore sigmaGen F₀ is a monotone class.

    have hFsub :
        F₀ ⊆ sigmaGen F₀ :=
      subset_sigmaGen F₀
    -- USE HELPER 5.
    --
    -- The generated σ-field contains
    -- its original generating collection.

    exact monoGen_minimal
      F₀ (sigmaGen F₀) hMonotone hFsub
    -- USE HELPER 2: Minimality.
    --
    -- sigmaGen F₀ is a monotone class
    -- containing F₀.
    --
    -- By minimality of the generated monotone class:
    --
    -- monoGen F₀ ⊆ sigmaGen F₀.
    --
    -- Direction 1 is proved.


  -- ----------------------------------------------------------
  -- DIRECTION 2: sigmaGen F₀ ⊆ monoGen F₀
  -- ----------------------------------------------------------

  · have hField :
        IsField (monoGen F₀) :=
      monoGen_isField F₀ hF₀
    -- USE LEMMA 3.
    --
    -- Since F₀ is a field,
    -- monoGen F₀ is also a field.

    have hMonotone :
        IsMonotoneClass (monoGen F₀) :=
      monoGen_isMonotoneClass F₀
    -- USE LEMMA 1.
    --
    -- monoGen F₀ is a monotone class.

    have hSigma :
        IsSigmaField (monoGen F₀) :=
      isSigmaField_of_field_monotone
        (monoGen F₀) hField hMonotone
    -- USE LEMMA 4.
    --
    -- monoGen F₀ is both a field
    -- and a monotone class.
    --
    -- Therefore monoGen F₀ is a σ-field.

    have hFsub :
        F₀ ⊆ monoGen F₀ :=
      subset_monoGen F₀
    -- USE HELPER 1.
    --
    -- monoGen F₀ contains F₀.

    intro E hE
    -- Introduce arbitrary E ∈ sigmaGen F₀.
    --
    -- hE : E ∈ sigmaGen F₀.
    -- Goal: E ∈ monoGen F₀.

    exact (Set.mem_sInter.mp hE)
      (monoGen F₀) ⟨hSigma, hFsub⟩
    -- sigmaGen F₀ is the intersection
    -- of all σ-fields containing F₀.
    --
    -- Since E ∈ sigmaGen F₀,
    -- E belongs to every such σ-field.
    --
    -- In particular, monoGen F₀ is eligible:
    --
    -- hSigma proves monoGen F₀ is a σ-field.
    -- hFsub proves F₀ ⊆ monoGen F₀.
    --
    -- Therefore E ∈ monoGen F₀.
    --
    -- Thus sigmaGen F₀ ⊆ monoGen F₀.
    --
    -- Direction 2 is proved.
    --
    -- Since both inclusions hold:
    --
    -- monoGen F₀ = sigmaGen F₀.
    --
    -- The Monotone Class Theorem is proved.

end Math7800.Midterm

#print axioms Math7800.Midterm.monoGen_isMonotoneClass
#print axioms Math7800.Midterm.monotone_class_of_sigmaField
#print axioms Math7800.Midterm.monoGen_isField
#print axioms Math7800.Midterm.isSigmaField_of_field_monotone
#print axioms Math7800.Midterm.monotone_class
