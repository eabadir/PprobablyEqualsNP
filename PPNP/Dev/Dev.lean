import EGPT.Core
import EGPT.Complexity.Core
import EGPT.Entropy.Common
import EGPT.Physics.PhysicsDist
import EGPT.NumberTheory.Core -- For ParticlePath, fromNat, toNat

open EGPT EGPT.Complexity EGPT.NumberTheory.Core EGPT.Constraints

lemma encodeLiteral_nonempty {k : ℕ} (l : Literal_EGPT k) : 0 < (encodeLiteral l).length := by
  unfold encodeLiteral
  simp [encodeNat, List.length_append, List.length_cons, List.length_replicate]

-- Helper lemma for proving properties of foldl with append
lemma foldl_append_distrib {α β} (g : α → List β) (init : List β) (l : List α) :
  (List.foldl (fun acc x => List.append acc (g x)) init l) = List.append init (List.foldl (fun acc x => List.append acc (g x)) [] l) := by
  induction l generalizing init with
  | nil => simp [List.foldl, List.append_nil]
  | cons h t ih =>
    simp only [List.foldl]
    rw [ih (List.append init (g h))]
    rw [ih (List.append [] (g h))]
    simp [List.nil_append, List.append_assoc]


-- Helper lemma to relate foldl with append to flatten and map
lemma foldl_append_flatten_map {α} (g : α → List Bool) (c : List α) :
  List.foldl (fun acc l => List.append acc (g l)) [] c = List.flatten (c.map g) := by
  induction c with
  | nil => simp [List.foldl, List.map, List.flatten]
  | cons head tail ih =>
    simp [List.foldl, List.map, List.flatten, ih]

-- Helper lemma: foldl with non-empty initial value has greater length
lemma foldl_append_length_ge {α : Type*} (init : List Bool) (g : α → List Bool) (l : List α) :
  0 < init.length →
  (List.foldl (fun acc x => List.append acc (g x)) [] l).length <
  (List.foldl (fun acc x => List.append acc (g x)) init l).length := by
  intro h_init_nonempty
  have h_eq : List.foldl (fun acc x => List.append acc (g x)) init l =
              List.append init (List.foldl (fun acc x => List.append acc (g x)) [] l) := by
    exact foldl_append_distrib g init l
  rw [h_eq]
  -- We need to prove that a.length < (List.append init a).length where a is the foldl result
  let a := List.foldl (fun acc x => List.append acc (g x)) [] l
  change a.length < (List.append init a).length
  -- Show that List.append is equivalent to ++
  have h_append_eq : List.append init a = init ++ a := by rfl
  rw [h_append_eq]
  -- Now use the standard length_append theorem
  rw [List.length_append]
  exact Nat.lt_add_of_pos_left h_init_nonempty

-- Helper lemma: encodeClause c ++ [false, false] is non-empty
lemma encodeClause_with_separators_nonempty {k : ℕ} (c : Clause_EGPT k) :
  0 < (List.append (encodeClause c) [false, false]).length := by
  simp [List.length_append, List.length_cons, List.length_nil]

-- Helper lemma: foldl with non-empty initial value and mapped list has greater length
lemma foldl_append_map_length_ge {α : Type*} (init : List Bool) (g : α → List Bool) (l : List α) :
  0 < init.length →
  (List.foldl List.append [] (List.map g l)).length <
  (List.foldl List.append init (List.map g l)).length := by
  intro h_init_nonempty
  -- We'll use the fact that List.map g l is just a list of List Bool
  let mapped := List.map g l
  -- Now we can use our existing lemma with identity function
  have h_eq : List.foldl List.append init mapped =
              List.append init (List.foldl List.append [] mapped) := by
    exact foldl_append_distrib (fun x => x) init mapped
  rw [h_eq]
  -- Show that List.append is equivalent to ++
  have h_append_eq : List.append init (List.foldl List.append [] mapped) =
                     init ++ (List.foldl List.append [] mapped) := by rfl
  rw [h_append_eq]
  -- Now use the standard length_append theorem
  rw [List.length_append]
  exact Nat.lt_add_of_pos_left h_init_nonempty




lemma length_encodeClause_eq_sum_of_lengths {k : ℕ} (c : Clause_EGPT k) :
  (encodeClause c).length = List.sum (c.map (fun l => (encodeLiteral l).length + 1)) := by
  let g : Literal_EGPT k → List Bool := fun l => List.append (encodeLiteral l) [false]
  have h_eq_join_map : encodeClause c = List.flatten (c.map g) := by
    unfold encodeClause
    exact foldl_append_flatten_map g c
  rw [h_eq_join_map]
  rw [List.length_flatten]
  simp only [List.map_map]
  congr 1
  ext l
  simp [g, Function.comp, List.length_append, List.length_cons, List.length_nil]

/--
Helper lemma: The encoding of a single clause is non-empty.

This is because `encodeClause` folds over the literals, appending `[false]`
for each one. Even an empty clause is mapped to `[false, false]` by the
outer `encodeCNF` call, but we can prove a simpler property here. The
`List.append` structure ensures the length increases.
-/
lemma encodeClause_nonempty {k : ℕ} (c : Clause_EGPT k) :
  c.length ≤ (encodeClause c).length := by
  rw [length_encodeClause_eq_sum_of_lengths]
  let f := fun l : Literal_EGPT k => (encodeLiteral l).length + 1
  change c.length ≤ List.sum (c.map f)
  have h_f_ge_1 : ∀ (l : Literal_EGPT k), 1 ≤ f l := by
    intro l
    unfold f
    have := encodeLiteral_nonempty l
    linarith [Nat.succ_le_of_lt this]
  induction c with
  | nil => simp [List.map, List.sum]
  | cons head tail ih =>
    simp [List.map, List.sum]
    have h_head_ge_1 : 1 ≤ f head := h_f_ge_1 head
    -- We want to show: tail.length + 1 ≤ f head + (List.map f tail).sum
    -- We have from ih: tail.length ≤ (List.map f tail).sum
    -- And from h_head_ge_1: 1 ≤ f head
    -- Note that List.sum is List.foldr (+) 0, so we need to handle the addition carefully
    have h_sum_eq : (List.map f tail).sum = List.foldr (fun x1 x2 => x1 + x2) 0 (List.map f tail) := by
      rfl
    rw [h_sum_eq] at ih
    have h_add_comm : f head + List.foldr (fun x1 x2 => x1 + x2) 0 (List.map f tail) =
                      List.foldr (fun x1 x2 => x1 + x2) 0 (List.map f tail) + f head := by
      rw [Nat.add_comm]
    rw [h_add_comm]
    linarith [ih, h_head_ge_1]

/--
Helper Lemma: The length of the `ComputerTape` generated by `encodeCNF`
strictly increases for each clause added.
-/
lemma encodeCNF_length_increases_with_clause {k : ℕ} (h : Literal_EGPT k) (t : SyntacticCNF_EGPT k) :
  (encodeCNF t).length < (encodeCNF ([h] :: t)).length := by
  -- Unfold the definition of encodeCNF to see the list construction
  unfold encodeCNF
  -- The core of encodeCNF is a fold. We can analyze how the fold changes.
  simp only [List.map_cons, List.foldl_cons, List.nil_append]
  -- Use a simple length inequality: adding a non-empty prefix increases length
  let g : Clause_EGPT k → List Bool := fun c => List.append (encodeClause c) [false, false]
  -- We need to show that adding g [h] as initial value to the fold increases the total length
  have h_g_nonempty : 0 < (g [h]).length := by
    simp [g, List.length_append]

  -- Use the fact that foldl with non-empty initial value has greater length
  have h_foldl_increase : (List.foldl List.append [] (List.map g t)).length <
                          (List.foldl List.append (g [h]) (List.map g t)).length := by
    -- This is true because foldl appends all elements, so starting with g [h] adds its length
    have h_eq : List.foldl List.append (g [h]) (List.map g t) =
                List.append (g [h]) (List.foldl List.append [] (List.map g t)) := by
      exact foldl_append_distrib (fun x => x) (g [h]) (List.map g t)
    simp [h_eq, List.length_append]
    exact Nat.lt_add_of_pos_left h_g_nonempty
  -- Apply this to the full expression
  simp [List.length_append]
  exact h_foldl_increase


/--
**Theorem: The length of an encoded CNF is at least the number of its clauses.**

This theorem is proven by induction on the list of clauses. It is a syntactic
proof about the structure of the `encodeCNF` function, demonstrating that each
clause contributes to the final tape's length. This cannot be proven from
semantic theorems like `constrainedSystem_equiv_SAT`.
-/
theorem encodeCNF_length_ge_num_clauses {k : ℕ} (cnf : SyntacticCNF_EGPT k) :
  cnf.length ≤ (encodeCNF cnf).length :=
by
  -- The modern idiom for list induction is `induction ... with`.
  induction cnf with
  | nil =>
    -- Base Case: cnf is the empty list `[]`.
    -- `[].length` is 0. `(encodeCNF []).length` is `k + 2`.
    -- The goal `0 ≤ k + 2` is always true for natural numbers.
    simp only [List.length, encodeCNF, List.map_nil, List.foldl_nil]
    simp only [List.length_append, Nat.add_zero, encodeNat]
    simp  [List.length_replicate, List.length_cons, List.length_nil]

  | cons head tail ih =>
    -- Inductive Step: Assume `tail.length ≤ (encodeCNF tail).length` (this is `ih`).
    -- Prove it for `head :: tail`.
    -- We use a `calc` block for a clear, readable chain of inequalities.
    calc
      -- Start with the LHS.
      (head :: tail).length
        = tail.length + 1 := by simp [List.length_cons]
      -- Use the induction hypothesis `ih`.
      _ ≤ (encodeCNF tail).length + 1 := by gcongr
      -- Show that adding a clause increases the encoded length by at least 1.
      _ ≤ (encodeCNF (head :: tail)).length := by
          -- Direct calculation approach
          unfold encodeCNF
          simp [List.map_cons, List.foldl_cons, List.nil_append]
          -- After simplification, we have an inequality between two foldl operations
          -- We need to use our helper lemma about foldl with non-empty initial values
          let g : Clause_EGPT k → List Bool := fun c => List.append (encodeClause c) [false, false]
          have h_g_nonempty : 0 < (g head).length := by
            simp only [g]
            exact encodeClause_with_separators_nonempty head
          -- Apply our helper lemma correctly
          have h_foldl_increase : (List.foldl List.append [] (List.map g tail)).length <
                                  (List.foldl List.append (g head) (List.map g tail)).length := by
            exact foldl_append_map_length_ge (g head) g tail h_g_nonempty
          -- Now we need to handle the encodeNat part and the final structure
          -- The inequality we need to prove involves the full structure with encodeNat
          -- We can use the fact that adding a positive quantity preserves the inequality
          have h_preserve : ∀ a b c : ℕ, b < c → a + (b + 1 + 1) + 1 ≤ a + (c + 1 + 1) := by
            intros a b c h_bc
            linarith
          -- Apply this preservation to our specific case
          apply h_preserve (List.length (encodeNat k))
          exact h_foldl_increase
