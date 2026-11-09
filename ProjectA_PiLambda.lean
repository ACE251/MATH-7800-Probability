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

lemma lambdaGen_isLambdaSys (A : Set (Set Ω)) : IsLambdaSys (lambdaGen A) := by
  unfold lambdaGen
    -- unfolds def of lambdaGen A
    -- R: show the set given by that definition is a lambda-sys
  constructor
    -- splits into conditions from definition of IsLambdaSys
    -- R: show all three condition for IsLambdaSyS hold for any L in the intersection
    --    univ_mem
    --    compl_mem
    --    iUnion_mem

  intro L hL
    -- select arbitrary L in the class
    -- R: show univ_mem ∈ L
  exact hL.1.univ_mem
    -- L is a lambda-sys, so must contain univ_mem
    -- R: 끝 wrt univ_mem

  intro B hB
    -- select arbitrary B in lambdaGen A
    -- R: show B ∈ lambdaGen A → B^c ∈ lambdaGen A
  intro L hL
    -- select L, an arbitrary lambda-sys containing A
    -- R: B^c ∈ L
  exact hL.1.compl_mem B (hB L hL)
    -- L is a lambda-sys, so it's closed on complements
    -- B is in the intersection of all L's so it's in L
    -- so B^c ∈ L
    -- R: 끝 wrt compl_mem

  intro f hdisj hf
    -- introduces the sequence of sets,
    -- pairwise disjointness,
    -- every set in the sequence belongs to the intersection.
    -- R: show union of f's is in intersection
  apply Set.mem_sInter.mpr
    -- says we must show the union belongs to every lambda system in the class.
    -- R: show ∀ L in intersection, union of f's is in L
  intro L hL
    -- select an arbitrary L
    -- R: show union of f's is in L
  apply hL.1.iUnion_mem f hdisj
    -- applies union-closure to the chosen L
    -- R: show each f is in L
  intro n
    -- select an arbitrary n
    -- R: show f is in L
  exact Set.mem_sInter.mp (hf n) L hL
    -- applies all f's in L for all L's
    -- R: 끝 wrt iUnion_mem

  -- R: 끝




lemma subset_lambdaGen (A : Set (Set Ω)) : A ⊆ lambdaGen A := by

  intro B hB
    -- select an arbitrary B inside A
    -- R: show B is in lambdaGen A
  unfold lambdaGen
    -- unfold I know this one
    -- R: show B is in lambdaGen A
  apply Set.mem_sInter.mpr
    -- from "in intersection" to "in each"
    -- R: show B is inside every L in the class
  intro L hL
    -- select an arbitrary L from lambdaGen A
    -- R: show B is in L
  exact hL.2 hB
    -- .2 pulls in the A ⊆ L condition of L being in the class
    -- R: 끝



lemma lambdaSys_cnts_empty (L : Set (Set Ω)) (hL : IsLambdaSys L) : ∅ ∈ L := by
  -- L is a set
  -- hL is that L is a lambda system
  -- R: ∅ is in L
  have h : univᶜ ∈ L := by
    -- save the fact that univ^c is in L to the name h
    -- R: show h true for all L in class
    exact hL.compl_mem univ hL.univ_mem
      -- since L is L-sys,
      -- it has complement of univ,
      -- which we know is in L bc L is a lambda-sys
      -- R: univ^c is in every L, so ∅ is in every L
  simp only [compl_univ] at h
    -- simplify univ^c to ∅
  exact h
    -- R: 끝



lemma finite_disjoint_union_mem
    (L : Set (Set Ω))
    (hL : IsLambdaSys L)
    (k : ℕ)
    (A : Fin k → Set Ω)
    (hdisj : Pairwise (Disjoint on A))
    (hmem : ∀ i, A i ∈ L) :
    (⋃ i, A i) ∈ L := by

  let f : ℕ → Set Ω := fun n =>
    if h : n < k then A ⟨n, h⟩ else ∅
    -- initialize f as the conditional
    -- if n < k, take f_n to be A_n,
    -- else take f_n = ∅

  have hfmem : ∀ n, f n ∈ L := by
    intro n
      -- choose arbitrary n
      -- R: show f_n ∈ L
    dsimp [f]
      -- unfold def of f_n
      -- R: show f_n = A_n and f_n = ∅ are both in L
    split
      -- split cases into
      -- f_n = A_n
      -- f_n = ∅
      -- R: show both in L
    · exact hmem _
        -- if f_n = A_n, duh
        -- R: 끝 wrt n < k
    · exact lambdaSys_cnts_empty L hL
        -- if f_n = ∅,
        -- L is a lambda-sys, so contains ∅
        -- R: 끝 wrt n ≥ k
      -- so ∀ n, f n ∈ L 끝

  have hfdisj : Pairwise (Disjoint on f) := by
    intro i j hij
      -- arbitrary i, j
      -- R: hij → f_i, f_j disjoint
    change Disjoint (f i) (f j)
    dsimp [f]
      -- R: if f_i and f_j are chosen as f is defined, they're disjoint
    split_ifs with hi hj
      -- split into cases by i < k or not, j < k or not, 4 cases
      -- R: show f_i and f_j disjoint in each case
    · have hne : (⟨i, hi⟩ : Fin k) ≠ (⟨j, hj⟩ : Fin k) := by
        intro heq
        -- asm f_i = f_j
        -- R: i = j
        exact hij (congrArg Fin.val heq)
          -- i = j ↔ f_i = f_j
          -- R: f_i = f_j
      exact hdisj hne
        -- but i ≠ j, so f_i, f_j are disj
        -- R: 끝 wrt i < k, j < k
    · simp
      -- j ≥ k, so f_j = ∅ which is disjoint from f_i
      -- R: 끝 wrt i < k, j ≥ k
    · simp
      -- i ≥ k, so f_i = ∅ which is disjoint from f_j
      -- R: 끝 wrt i ≥ k, j < k
    · simp
      -- j ≥ k and i ≥ k, so f_i, f_j = ∅ which are disjoint from each other
      -- R: 끝 wrt i ≥ k, j ≥ k
    -- R: 끝

  have hunion : (⋃ n, f n) = ⋃ i, A i := by
    -- union across n's of f_n's is the same as the union across i's of A_i's
    -- R: U f_n = U A_i
    ext x
      -- arbitrary x from U f_n is in U A_i and vice versa
      -- R: ∀ x, x ∈ U f_n ↔ x ∈ U A_i
    simp only [Set.mem_iUnion]
      -- find element from each union containing x
      -- R: ∃ i st x ∈ f_i ↔ ∃ i st x ∈ A_i
    constructor
      -- split into 2 directed conditionals
      -- R: ∃ i st x ∈ f_i -> ∃ i st x ∈ A_i
      --  ∧ ∃ i st x ∈ f_i <- ∃ i st x ∈ A_i
    · rintro ⟨n, hn⟩
        -- asm ∃ n st f_n contains x
        -- R: ∃ i st A_i contains x
      by_cases h : n < k
        -- first case is n < k
        -- R: ∃ i, x ∈ A_i
      · refine ⟨⟨n, h⟩, ?_⟩
          -- ⟨ n ,
          -- n < k ⟩ ,
          -- R: x ∈ A_⟨n, h⟩
        simpa [f, h] using hn
          -- f is "if n < k, choose A_n, else choose ∅"
          -- R: 끝 wrt ∃ i st x ∈ f_i -> ∃ i st x ∈ A_i
      · simp [f, h] at hn
          -- n ≥ k means f_n is a null set, which can't contain x
          -- f is "if n < k, choose A_n, else choose ∅"
          -- R: 끝 wrt ∃ i st x ∈ f_i -> ∃ i st x ∈ A_i
    · rintro ⟨i, hi⟩
        -- asm ∃ i st A_i contains x
        -- R: ∃ f st f_n contains x
      exact ⟨i.val, by simpa [f, i.isLt] using hi⟩
        -- f_n was chosen based on A_i's
        -- R: 끝 wrt ∃ i st x ∈ f_i <- ∃ i st x ∈ A_i
  rw [← hunion]
    -- works for finite union, so can be written in terms of cntbl union
    -- R: show if it works for finite union,
    --    we can apply union closure of lambda-sys
  exact hL.iUnion_mem f hfdisj hfmem
    -- apply union closure since f is infinite,
    -- f_n's are disj,
    -- and each f_n is in L
    -- R: 끝



lemma lambdaSys_diff
    (L : Set (Set Ω))
    (hL : IsLambdaSys L)
    (B C : Set Ω)
    (hB : B ∈ L)
    (hC : C ∈ L)
    (hBC : B ⊆ C) :
    C \ B ∈ L := by

  have hCc : Cᶜ ∈ L := by
    -- want to use complements
    -- R: Cᶜ ∈ L
    exact hL.compl_mem C hC
      -- since C ∈ L, and L is a lambda-sys, Cᶜ ∈ L
      -- R: 끝

  have hdisj : Disjoint B Cᶜ := by
    -- remember B ⊆ C
    -- R: B ∩ C^c = ∅
    apply Set.disjoint_left.mpr
      -- (x ∈ B → x ∉ C^c) implies B, C^c disjoint
      -- R: x ∈ B → x ∉ C^c
    intro xx hxB hxCc
      -- select arbitrary xx, asm in both B and C^c
      -- R: contradiction
    exact hxCc (hBC hxB)
      -- xx required to be in both C and C^c
      -- R: 끝

  have hUnion : B ∪ Cᶜ ∈ L := by
    let f : Fin 2 → Set Ω := ![B, Cᶜ]
    -- make an array f_n with f_0 = B, f_1 = C^c
    -- R: B ∪ Cᶜ ∈ L

    have hfmem : ∀ i, f i ∈ L := by
      -- both are in L
      -- R: ∀ (i : Fin 2), f i ∈ L
      intro i
        -- arbitrary i from {0,1}
        -- R: f_i ∈ L
      fin_cases i
        -- splits into finite cases
        -- R: show for i = 0, i = 1
      · exact hB
          -- works for i = 0
      · exact hCc
          -- works for i = 1
      -- R: 끝

    have hfdisj : Pairwise (Disjoint on f) := by
      -- WTS f_0 and f_1 are disj
      intro i j hij
        -- select i,j st i ≠ j
        -- R: f_i, f_j are disj
      fin_cases i <;> fin_cases j
        -- finite number of cases for both i and j
        -- R: f_i, f_j are disj in each case
      · exact False.elim (hij rfl)
          -- i = 0, j = 0; not allowed since i ≠ j
      · exact hdisj
        -- i = 0, j = 1; B and C^c are disj by prev hdisj
      · exact hdisj.symm
        -- i = 1, j = 0; C^c and B are disj by prev hdisj
      · exact False.elim (hij rfl)
        -- i = 1, j = 1; not allowed since i ≠ j
      -- R: 끝

    have hEq : (⋃ i, f i) = B ∪ Cᶜ := by
      -- R: need to show U f_0, f_1 = U B, C^c
      ext x
        -- R: x ∈ ⋃ i, f i ↔ x ∈ B ∪ Cᶜ
      simp only [Set.mem_iUnion, Set.mem_union]
        -- unfold being in U f_0, f_1
        -- R: (∃ i, x ∈ f i) ↔ x ∈ B ∨ x ∈ Cᶜ
      constructor
        -- split biconditional into 2 conditionals
      · rintro ⟨i, hi⟩
          -- asm x is in f_i for some i
          -- R: x ∈ B ∨ x ∈ Cᶜ
        fin_cases i
          -- finite number of cases for i
          -- R: show x ∈ B or x ∈ Cᶜ in each case
        · exact Or.inl (by simpa [f] using hi)
            -- if x ∈ f_0, x ∈ B
        · exact Or.inr (by simpa [f] using hi)
            -- if x ∈ f_0, x ∉ C
          -- R: 끝 wrt (∃ i, x ∈ f i) → x ∈ B ∨ x ∈ Cᶜ
      · intro hx
        -- asm x is in B or x is in Cᶜ
        -- R: ∃ i, x ∈ f i
        rcases hx with hxB | hxCc
          -- cases are x ∈ B or x ∈ Cᶜ
        · exact ⟨0, by simpa [f] using hxB⟩
            -- x ∈ f_0 if x ∈ B
        · exact ⟨1, by simpa [f] using hxCc⟩
            -- x ∈ f_1 if x ∈ Cᶜ
        -- R: 끝 wrt x ∈ B ∨ x ∈ Cᶜ → (∃ i, x ∈ f i)

    have h := finite_disjoint_union_mem L hL 2 f hfdisj hfmem
      -- the union of any 2 f's from L is in L,
      -- since L is a lambda-sys
      -- R: B and C^c are such f's
    rw [← hEq]
      -- union of B and C^c is the union of f's
    exact h
      -- R: 끝

  have hComp : (B ∪ Cᶜ)ᶜ ∈ L := by
    exact hL.compl_mem (B ∪ Cᶜ) hUnion
     -- by hUnion, (B ∪ Cᶜ) ∈ L, so
     -- (B ∪ Cᶜ)ᶜ ∈ L since L is a lambda-sys (closure on compl)

  have hEq : (B ∪ Cᶜ)ᶜ = C \ B := by
    ext x
     -- sets contain same elements
     -- R: x ∈ (B ∪ Cᶜ)ᶜ ↔ x ∈ C \ B
    simp only [Set.mem_compl_iff, Set.mem_union,
      Set.mem_sdiff, not_or, not_not]
      -- simplify by set notation properties/definitions
      -- R: x ∉ B ∧ x ∈ C ↔ x ∈ C ∧ x ∉ B
    tauto
      -- symmetry of ∧
      -- R: 끝

  rw [← hEq]
  exact hComp
    -- so C \ B ∈ L



lemma lambdaGen_inter (P : Set (Set Ω)) (hP : IsPiSys P) :
    ∀ A ∈ lambdaGen P, ∀ B ∈ lambdaGen P, A ∩ B ∈ lambdaGen P := by

  have h₁ : ∀ A ∈ P, ∀ B ∈ lambdaGen P,
      A ∩ B ∈ lambdaGen P := by
      -- show closure under intersecting with a set from the original pi-sys
    intro A hA
      -- select A from P
      -- R: ∀ B ∈ lambdaGen P, A ∩ B ∈ lambdaGen P

    let D : Set (Set Ω) :=
      {B | B ∈ lambdaGen P ∧ A ∩ B ∈ lambdaGen P}
      -- the set of sets that work
      -- R: D = lambdaGen P
    have hD : IsLambdaSys D := by
      constructor
        -- split into 3 conditions needed for lambda-sys
      · change univ ∈ lambdaGen P ∧ A ∩ univ ∈ lambdaGen P
          -- unfold membership in D
          -- R: exactly the change: univ ∈ lambdaGen P ∧ A ∩ univ ∈ lambdaGen P
        constructor
          -- split into the sides of the and
          -- R:     univ ∈ lambdaGen P ∧
          --    A ∩ univ ∈ lambdaGen P
        · exact (lambdaGen_isLambdaSys P).univ_mem
            -- lambdaGen P is a lambda-sys so contains univ
        · simpa using (subset_lambdaGen P hA)
            -- A ∩ univ = A,
            -- A is in lambdaGen A by subset_lambdaGen
          -- R: 끝 wrt univ_mem

      · intro B hB
          -- select B from D
          -- R: B^c ∈ D
        unfold D at hB ⊢
          -- unfold D, use ⊢ to force it to talk abt B^c
          -- R: B^c in the class D
        rcases hB with ⟨hBgen, hABgen⟩
          -- split both sides of the and
          -- R: B ∈ lambdaGen P ∧
          --    A U B ∈ lambdaGen P
        constructor
          -- examine B^c under both conditions
          -- R: B^c ∈ lambdaGen P ∧
          --    A U B^c ∈ lambdaGen P
        · exact (lambdaGen_isLambdaSys P).compl_mem B hBgen
            -- B^c in lambdaGen P since B was in lambdaGen P
        · have hAgen : A ∈ lambdaGen P :=
            subset_lambdaGen P hA
            -- A is in lambdaGen P bc A is in P
            -- R: A ∩ Bᶜ ∈ lambdaGen P
          have hDiff : A \ (A ∩ B) ∈ lambdaGen P := by
            apply lambdaSys_diff (lambdaGen P) (lambdaGen_isLambdaSys P) (A ∩ B) A
              -- lambdaSys_diff takes
              --  set of sets           -> (lambdaGen P)
              --  that is a lambda-sys  -> (lambdaGen_isLambdaSys P)
              --  pair of sets          -> (A ∩ B), A
              --  each is in the set of sets -> need
              --  one is inside the other ->    need
              -- provides bigger \ smaller is in set of sets
            · exact hABgen
                -- each is in the set of sets 1
            · exact hAgen
                -- each is in the set of sets 2
            · exact Set.inter_subset_left
                -- one is inside the other
          have hEq : A \ (A ∩ B) = A ∩ Bᶜ := by
            ext x
              -- switch set equality to membership equivalence
              -- R: x ∈ A \ (A ∩ B) ↔ x ∈ A ∩ Bᶜ
            simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff]
              -- simplify using set properties/definitions
              -- R: x ∈ A ∧ ¬(x ∈ A ∧ x ∈ B) ↔ x ∈ A ∧ x ∉ B
            tauto
              -- absorption?
          rw [← hEq]
            -- A \ (A ∩ B) = A ∩ Bᶜ
          exact hDiff
            -- A ∩ Bᶜ ∈ P
            -- R: 끝 wrt compl_mem

      · intro f hfdisj hfmem
          -- select disj f's from D
          -- R: ⋃ n, f n ∈ D
        change ∀ n, f n ∈ lambdaGen P ∧
          A ∩ f n ∈ lambdaGen P at hfmem
        change (⋃ n, f n) ∈ lambdaGen P ∧
          A ∩ (⋃ n, f n) ∈ lambdaGen P
          -- unfold membership in D
          -- R: ⋃ n, f n ∈ lambdaGen P ∧
          --    A ∩ ⋃ n, f n ∈ lambdaGen P
        constructor
          -- split into the two conditions
          -- R: show U of f's meets both
        · apply (lambdaGen_isLambdaSys P).iUnion_mem f hfdisj
            -- since lambdaGen P is a lambda-sys, union of things in it will be in it
            -- R: each f n ∈ lambdaGen P
          intro n
            -- choose arbitrary n
            -- R: f n ∈ lambdaGen P
          exact (hfmem n).1
            -- f_n was chosen to be in lambdaGen P since its in D
          -- R: 끝 wrt U of f's ∈ lambdaGen P

        · let g : ℕ → Set Ω := fun n => A ∩ f n
          have hgmem : ∀ n, g n ∈ lambdaGen P := by
            -- new sequence g_n where g_i = A ∩ f_i
            -- R: U g_n ∈ lambdaGen P
            intro n
              -- choose arbitrary n
              -- R: g n ∈ lambdaGen P
            exact (hfmem n).2
              -- g_n is in lambdaGen P by choosing f_n ∈ D

          have hgdisj : Pairwise (Disjoint on g) := by
            intro i j hij
              -- choose disjoint i,j
              -- R: g_i, g_j are disj
            apply Set.disjoint_left.mpr
              -- membership must be exclusive between g_i,g_j
              -- R: a ∈ g i → a ∉ g j
            intro x hxi hxj
              -- choose x in g_i, g_j
              -- R: contradiction
            have hfi : x ∈ f i := hxi.2
              -- x ∈ g_i → x ∈ f_i
            have hfj : x ∈ f j := hxj.2
              -- x ∈ g_j → x ∈ f_j
            exact (Set.disjoint_left.mp (hfdisj hij)) hfi hfj
              -- since f_i,f_j disj, g_i,g_j must be disj
            -- so g_i,g_j mre disj

          have hUnion : (⋃ n, g n) ∈ lambdaGen P := by
            exact (lambdaGen_isLambdaSys P).iUnion_mem g hgdisj hgmem
            -- U g_n in lambdaGen P since they're disj members of lambdaGen P
          have hEq : (⋃ n, g n) = A ∩ (⋃ n, f n) := by
            -- undistribute A back out from g_n's
            -- R: U g_n = A ∩ (U f_n)
            ext x
              -- switch set equality to membership equivalence
              -- R: x ∈ ⋃ g_n ↔ x ∈ A ∩ ⋃ f_n
            simp only [Set.mem_iUnion, Set.mem_inter_iff]
              -- need to show both sides of and in A ∩ ⋃ f_n
              -- R: x ∈ A ∧
              --    ∃ i st x ∈ f_i
            constructor
              -- split biconditional into 2 conditionals
            · rintro ⟨n, hn⟩
              -- asm x ∈ g_n
              -- R: x ∈ A ∧ ∃ i, x ∈ f i
              exact ⟨hn.1, ⟨n, hn.2⟩⟩
                -- g_n ⊆ A so x ∈ A
                -- g_n ⊆ f_n so ∃ i, x ∈ f_i
            · rintro ⟨hxA, n, hxn⟩
              -- asm x ∈ A ∧ ∃ i, x ∈ f i
              -- R: ∃ i, x ∈ g_i
              exact ⟨n, ⟨hxA, hxn⟩⟩
                -- in both A and f_n means in g_n
          rw [← hEq]
          exact hUnion
            -- R: 끝 wrt ⋃ g_n ∈ lambdaGen P

    have hPD : P ⊆ D := by
      intro B hB
        -- select arbitray B ∈ P
        -- R: B ∈ D
      change B ∈ lambdaGen P ∧ A ∩ B ∈ lambdaGen P
        -- unfold membership in D
        -- R: B ∈ lambdaGen P ∧ A ∩ B ∈ lambdaGen P
      constructor
        -- split the and into both conditions for membership in D
        -- R: show B meets both
      · exact subset_lambdaGen P hB
          -- B was chosen from P, so clearly in lambdaGen P
      · apply subset_lambdaGen P
          -- B was chosen from P
        exact hP A hA B hB
          -- A also in P
          -- Pi-sys closed on int
          -- so A ∩ B ∈ P
        -- so B is in D

    have hGenD : lambdaGen P ⊆ D := by
      intro B hB
        -- choose arbitrary B in lambdaGen P
        -- R: B ∈ D
      unfold lambdaGen at hB
        -- unfold membership in lambdaGen P
      exact Set.mem_sInter.mp hB D ⟨hD, hPD⟩
        -- D is both a lambda-sys and contains P
        -- so its a member of the intersection defining lambdaGen P
      -- so lambdaGen P ⊆ D

    intro B hB
      -- choose arbitrary B ∈ lambdaGen P
      -- R: A ∩ B ∈ lambdaGen P
    have hBD : B ∈ D := hGenD hB
      -- by previous work, B ∈ D
    exact hBD.2
      -- by def of D, we have A ∩ B ∈ lambdaGen P
  -- R: 끝 wrt h_1

  let E : Set (Set Ω) :=
    {A | A ∈ lambdaGen P ∧
      ∀ B ∈ lambdaGen P, A ∩ B ∈ lambdaGen P}
    -- vary A, lambdaGen P has to be contained by the associated D

  -- similar to proof of D being a lambda-system
  have hE : IsLambdaSys E := by
    constructor
    · -- univ_mem
      change univ ∈ lambdaGen P ∧
        ∀ B ∈ lambdaGen P, univ ∩ B ∈ lambdaGen P
      constructor
      · exact (lambdaGen_isLambdaSys P).univ_mem
      · intro B hB
        simpa using hB

    · -- compl_mem
      intro A hA
      change A ∈ lambdaGen P ∧
        (∀ B ∈ lambdaGen P, A ∩ B ∈ lambdaGen P) at hA
      change Aᶜ ∈ lambdaGen P ∧
        ∀ B ∈ lambdaGen P, Aᶜ ∩ B ∈ lambdaGen P
      rcases hA with ⟨hAgen, hAinter⟩
      constructor
      · exact (lambdaGen_isLambdaSys P).compl_mem A hAgen
      · intro B hB
        have hDiff : B \ (A ∩ B) ∈ lambdaGen P := by
          apply lambdaSys_diff (lambdaGen P)
            (lambdaGen_isLambdaSys P) (A ∩ B) B
          · exact hAinter B hB
          · exact hB
          · exact Set.inter_subset_right
        have hEq : B \ (A ∩ B) = Aᶜ ∩ B := by
          ext x
          simp only [Set.mem_sdiff, Set.mem_inter_iff,
            Set.mem_compl_iff]
          tauto
        rw [← hEq]
        exact hDiff

    · -- iUnion_mem
      intro f hfdisj hfmem
      change ∀ n, f n ∈ lambdaGen P ∧
        (∀ B ∈ lambdaGen P, f n ∩ B ∈ lambdaGen P) at hfmem
      change (⋃ n, f n) ∈ lambdaGen P ∧
        ∀ B ∈ lambdaGen P,
          (⋃ n, f n) ∩ B ∈ lambdaGen P
      constructor
      · apply (lambdaGen_isLambdaSys P).iUnion_mem f hfdisj
        intro n
        exact (hfmem n).1
      · intro B hB
        let g : ℕ → Set Ω := fun n => f n ∩ B
        have hgmem : ∀ n, g n ∈ lambdaGen P := by
          intro n
          exact (hfmem n).2 B hB
        have hgdisj : Pairwise (Disjoint on g) := by
          intro i j hij
          apply Set.disjoint_left.mpr
          intro x hxi hxj
          exact (Set.disjoint_left.mp (hfdisj hij)) hxi.1 hxj.1
        have hUnion : (⋃ n, g n) ∈ lambdaGen P := by
          exact (lambdaGen_isLambdaSys P).iUnion_mem g hgdisj hgmem
        have hEq : (⋃ n, g n) = (⋃ n, f n) ∩ B := by
          ext x
          simp only [Set.mem_iUnion, Set.mem_inter_iff]
          constructor
          · rintro ⟨n, hn⟩
            exact ⟨⟨n, hn.1⟩, hn.2⟩
          · rintro ⟨⟨n, hxn⟩, hxB⟩
            exact ⟨n, ⟨hxn, hxB⟩⟩
        rw [← hEq]
        exact hUnion

  have hPE : P ⊆ E := by
    intro A hA
      -- choose arbitrary A ∈ P
      -- R: A ∈ E
    change A ∈ lambdaGen P ∧
      ∀ B ∈ lambdaGen P, A ∩ B ∈ lambdaGen P
      -- unfold membership in E
    constructor
      -- split into both sides of the and
    · exact subset_lambdaGen P hA
    · exact h₁ A hA

  have hGenE : lambdaGen P ⊆ E := by
    intro A hA
      -- choose arbitrary A ∈ lambdaGen P
      -- R: A ∈ E
    unfold lambdaGen at hA
    exact Set.mem_sInter.mp hA E ⟨hE, hPE⟩

  intro A hA B hB
    -- choose arbitrary A,B from lambdaGen P
  have hAE : A ∈ E := hGenE hA
    -- A in is class E since lambdaGen P ⊆ E
  exact hAE.2 B hB
    -- so A ∩ B ∈ lambdaGen P





lemma isSigmaField_of_lambda_pi
  (L : Set (Set Ω))
  (hL : IsLambdaSys L)
  (hπ : ∀ A ∈ L, ∀ B ∈ L, A ∩ B ∈ L) :
  IsSigmaField L := by
  classical
  -- closure on arbitrary intersection inside a lambda-sys means
  -- its a sigma field

  have hdiff : ∀ A ∈ L, ∀ B ∈ L, A \ B ∈ L := by
    -- L closed on set difference
    intro A hA B hB
      -- select arbitrary A,B from L
      -- R: A \ B ∈ L
    rw [Set.sdiff_eq]
      -- A \ B ∈ L  =  A ∩ Bᶜ ∈ L
      -- R: A ∩ Bᶜ ∈ L
    exact hπ A hA Bᶜ (hL.compl_mem B hB)
      -- by assumption, L closed on intersections
      -- B^c in L bc B is, and L is lambda-sys
      -- so A ∩ Bᶜ ∈ L
    -- so A \ B ∈ L

  have hunion : ∀ A ∈ L, ∀ B ∈ L, A ∪ B ∈ L := by
    -- for arbitrary (non-disjoint) A,B in L
    -- R: A ∪ B ∈ L
    intro A hA B hB
      -- select arbitrary A,B ∈ L
    have hAc : Aᶜ ∈ L := hL.compl_mem A hA
      -- A^c in L since A ∈ L and lamnda-sys
    have hBc : Bᶜ ∈ L := hL.compl_mem B hB
      -- B^c in L since B ∈ L and lamnda-sys
    have hInter : Aᶜ ∩ Bᶜ ∈ L :=
      hπ Aᶜ hAc Bᶜ hBc
      -- from assumption, L is closed on intersection
      -- so Aᶜ ∩ Bᶜ ∈ L
    have hComp : (Aᶜ ∩ Bᶜ)ᶜ ∈ L :=
      hL.compl_mem (Aᶜ ∩ Bᶜ) hInter
      -- since Aᶜ ∩ Bᶜ ∈ L, its complement is as well
      -- (Aᶜ ∩ Bᶜ)ᶜ ∈ L
    simpa only [compl_inter, compl_compl] using hComp
      -- simplify (Aᶜ ∩ Bᶜ)ᶜ to A U B using set properties
    -- so arbitrary A,B from L have A U B in L

  constructor
  · -- univ_mem
    exact hL.univ_mem
  · -- compl_mem
    exact hL.compl_mem
  · -- iUnion_mem
    intro f hfmem
    -- select arbitrary sequence of f's all from L
    -- R: U f_i ∈ L

    -- The union of the first n sets.
    let U : ℕ → Set Ω := fun n => ⋃ k : Fin n, f k.val

    have hUmem : ∀ n, U n ∈ L := by
      -- each finite union in is L
      -- R: ∀ (n : ℕ), U n ∈ L
      intro n
        -- select n
        -- R: U n ∈ L
      induction n with
      | zero =>
          change (⋃ k : Fin 0, f k.val) ∈ L
          simpa using (lambdaSys_cnts_empty L hL)
          -- f_0 = ∅
          -- so f_0 ∈ L
      | succ n ih =>
          -- R: U of first n+1 f_n' is in L
          have hEq : U (n + 1) = U n ∪ f n := by
            ext x
              -- set equality to membership conditions
              -- R: x ∈ U (n + 1) ↔ x ∈ U n ∪ f n
            simp only [U, Set.mem_iUnion, Set.mem_union]
              -- union membership to union member membership
              -- R: (∃ i, x ∈ f ↑i) ↔ (∃ i, x ∈ f ↑i) ∨ x ∈ f n
            constructor
              -- split biconditional to both conditionals
              -- show x's membership implies both directions
            · rintro ⟨k, hk⟩
                -- x in union of first n+1
              by_cases h : k.val < n
                -- x in union of first n, or in the n+1-th
              · exact Or.inl ⟨⟨k.val, h⟩, hk⟩
                  -- if in union of first n, theres an index for its f
              · have heq : k.val = n := by omega
                exact Or.inr (by simpa [heq] using hk)
                  -- its in f_n+1 its in f_n+1
              -- so x is in union of first n+1 f's
            · intro hx
                -- asm x in union of first n f's, or in f_n+1
                -- R: show ∃ i, x ∈ f_i
              rcases hx with ⟨k, hk⟩ | hx
                -- split into U f_n vs f_n+1
              · exact ⟨⟨k.val, by omega⟩, hk⟩
              · exact ⟨⟨n, by omega⟩, hx⟩
                -- either way, theres an i st x ∈ f_i
          rw [hEq]
          exact hunion (U n) ih (f n) (hfmem n)
      -- so union of arbitrary f's from L is in L

    -- Remove all earlier sets from f n.
    let g : ℕ → Set Ω := fun n => f n \ U n

    have hgmem : ∀ n, g n ∈ L := by
      intro n
      exact hdiff (f n) (hfmem n) (U n) (hUmem n)
      -- each g_n is in L since each f_n and finite union is in L
      -- and we have closure in L on all the operations we need to construct g_n's

    have hgdisj : Pairwise (Disjoint on g) := by
      intro i j hij
      -- select distinct i,j
      -- R: g_i, g_j disjoint
      apply Set.disjoint_left.mpr
      intro x hxi hxj
        -- assume x in both
        -- R: contradiction
      rcases lt_or_gt_of_ne hij with hijlt | hjilt
        -- if i ≠ j, either i < j or j < i
      · have hxU : x ∈ U j := by
          exact Set.mem_iUnion.mpr
            ⟨⟨i, hijlt⟩, hxi.1⟩
            -- x ∈ g_i, so its in f_i
            -- R: contradiction
        exact hxj.2 hxU
          -- x ∈ g_j, so it cant be in any f_i with i < j
          -- R: 끝 wrt contr
      · have hxU : x ∈ U i := by
          exact Set.mem_iUnion.mpr
            ⟨⟨j, hjilt⟩, hxj.1⟩
            -- x ∈ g_j, so its in f_j
            -- R: contradiction
        exact hxi.2 hxU
          -- x ∈ g_i, so it cant be in any f_j with j < i
          -- R: 끝 wrt contr
      -- so all g's are disj

    have hEq : (⋃ n, g n) = ⋃ n, f n := by
      ext x
        -- set equality to membership cond
        -- R: x ∈ ⋃ g_n ↔ x ∈ ⋃ f_n
      simp only [Set.mem_iUnion]
        -- union to exists in specific
        -- R: ∃ i st x ∈ g_i ↔ ∃ i st x ∈ f_i
      constructor
        -- split bic into 2 cond
      · rintro ⟨n, hn⟩
        exact ⟨n, hn.1⟩
          -- if x ∈ g_i, it was in f_i
      · rintro ⟨n, hn⟩
        -- Choose the first index where x appears.
        let m := Nat.find
          (show ∃ k, x ∈ f k from ⟨n, hn⟩)
        have hm : x ∈ f m := Nat.find_spec
          (show ∃ k, x ∈ f k from ⟨n, hn⟩)
          -- m is the lowest index for which x ∈ f_m
        have hnot : x ∉ U m := by
          intro hxU
          rcases Set.mem_iUnion.mp hxU with ⟨k, hk⟩
          -- x is not in any of the f_i's with lower index than m
          have hlt : k.val < m := k.isLt
          have hmin : m ≤ k.val :=
            Nat.find_min' (show ∃ k, x ∈ f k from ⟨n, hn⟩) hk
          omega
          -- x is in f_m but not in f_k for any k < m
        exact ⟨m, ⟨hm, hnot⟩⟩
        -- so we have an index making x ∈ f_i true

    rw [← hEq]
    exact hL.iUnion_mem g hgdisj hgmem
      -- arbitrary union of elements from L is in L
  -- R: 끝






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
