Sorting algorithms on lists 
In this file we define List.Sorted r l to be an alias for List.Pairwise r l. This alias is preferred in the case that r is a < or ≤-like relation. Then we define the sorting algorithm List.insertionSort and prove its correctness.

The predicate List.Sorted 
source
def List.Sorted{α : Type u_1} (R : α → α → Prop) :
List α → Prop
Sorted r l is the same as List.Pairwise r l, preferred in the case that r is a < or ≤-like relation (transitive and antisymmetric or asymmetric)

Equations
Instances For
source
instance List.decidableSorted{α : Type u} {r : α → α → Prop} [DecidableRel r] (l : List α) :
Decidable (Sorted r l)
Equations
source
theorem List.Sorted.le_of_lt{α : Type u} [Preorder α] {l : List α} (h : Sorted (fun (x1 x2 : α) => x1 < x2) l) :
Sorted (fun (x1 x2 : α) => x1 ≤ x2) l
source
theorem List.Sorted.lt_of_le{α : Type u} [PartialOrder α] {l : List α} (h₁ : Sorted (fun (x1 x2 : α) => x1 ≤ x2) l) (h₂ : l.Nodup) :
Sorted (fun (x1 x2 : α) => x1 < x2) l
source
theorem List.Sorted.ge_of_gt{α : Type u} [Preorder α] {l : List α} (h : Sorted (fun (x1 x2 : α) => x1 > x2) l) :
Sorted (fun (x1 x2 : α) => x1 ≥ x2) l
source
theorem List.Sorted.gt_of_ge{α : Type u} [PartialOrder α] {l : List α} (h₁ : Sorted (fun (x1 x2 : α) => x1 ≥ x2) l) (h₂ : l.Nodup) :
Sorted (fun (x1 x2 : α) => x1 > x2) l
source
@[simp]
theorem List.sorted_nil{α : Type u} {r : α → α → Prop} :
Sorted r []
source
theorem List.Sorted.of_cons{α : Type u} {r : α → α → Prop} {a : α} {l : List α} :
Sorted r (a :: l) → Sorted r l
source
theorem List.Sorted.tail{α : Type u} {r : α → α → Prop} {l : List α} (h : Sorted r l) :
Sorted r l.tail
source
theorem List.rel_of_sorted_cons{α : Type u} {r : α → α → Prop} {a : α} {l : List α} :
Sorted r (a :: l) → ∀ b ∈ l, r a b
source
theorem List.Sorted.cons{α : Type u} {r : α → α → Prop} [IsTrans α r] {l : List α} {a b : α} (hab : r a b) (h : Sorted r (b :: l)) :
Sorted r (a :: b :: l)
source
theorem List.sorted_cons_cons{α : Type u} {r : α → α → Prop} [IsTrans α r] {l : List α} {a b : α} :
Sorted r (b :: a :: l) ↔ r b a ∧ Sorted r (a :: l)
source
theorem List.Sorted.head!_le{α : Type u} [Inhabited α] [Preorder α] {a : α} {l : List α} (h : Sorted (fun (x1 x2 : α) => x1 < x2) l) (ha : a ∈ l) :
l.head! ≤ a
source
theorem List.Sorted.le_head!{α : Type u} [Inhabited α] [Preorder α] {a : α} {l : List α} (h : Sorted (fun (x1 x2 : α) => x1 > x2) l) (ha : a ∈ l) :
a ≤ l.head!
source
@[simp]
theorem List.sorted_cons{α : Type u} {r : α → α → Prop} {a : α} {l : List α} :
Sorted r (a :: l) ↔ (∀ b ∈ l, r a b) ∧ Sorted r l
source
theorem List.Sorted.nodup{α : Type u} {r : α → α → Prop} [IsIrrefl α r] {l : List α} (h : Sorted r l) :
l.Nodup
source
theorem List.Sorted.filter{α : Type u} {r : α → α → Prop} {l : List α} (f : α → Bool) (h : Sorted r l) :
Sorted r (filter f l)
source
theorem List.eq_of_perm_of_sorted{α : Type u} {r : α → α → Prop} [IsAntisymm α r] {l₁ l₂ : List α} (hp : l₁.Perm l₂) (hs₁ : Sorted r l₁) (hs₂ : Sorted r l₂) :
l₁ = l₂
source
theorem List.Sorted.eq_of_mem_iff{α : Type u} {r : α → α → Prop} [IsAntisymm α r] [IsIrrefl α r] {l₁ l₂ : List α} (h₁ : Sorted r l₁) (h₂ : Sorted r l₂) (h : ∀ (a : α), a ∈ l₁ ↔ a ∈ l₂) :
l₁ = l₂
source
theorem List.sublist_of_subperm_of_sorted{α : Type u} {r : α → α → Prop} [IsAntisymm α r] {l₁ l₂ : List α} (hp : l₁.Subperm l₂) (hs₁ : Sorted r l₁) (hs₂ : Sorted r l₂) :
l₁.Sublist l₂
source
@[simp]
theorem List.sorted_singleton{α : Type u} {r : α → α → Prop} (a : α) :
Sorted r [a]
source
theorem List.sorted_lt_range(n : ℕ) :
Sorted (fun (x1 x2 : ℕ) => x1 < x2) (range n)
source
theorem List.sorted_replicate{α : Type u} {r : α → α → Prop} (n : ℕ) (a : α) :
Sorted r (replicate n a) ↔ n ≤ 1 ∨ r a a
source
theorem List.sorted_le_replicate{α : Type u} (n : ℕ) (a : α) [Preorder α] :
Sorted (fun (x1 x2 : α) => x1 ≤ x2) (replicate n a)
source
theorem List.sorted_le_range(n : ℕ) :
Sorted (fun (x1 x2 : ℕ) => x1 ≤ x2) (range n)
source
theorem List.sorted_lt_range'(a b : ℕ) {s : ℕ} (hs : s ≠ 0) :
Sorted (fun (x1 x2 : ℕ) => x1 < x2) (range' a b s)
source
theorem List.sorted_le_range'(a b s : ℕ) :
Sorted (fun (x1 x2 : ℕ) => x1 ≤ x2) (range' a b s)
source
theorem List.Sorted.rel_get_of_lt{α : Type u} {r : α → α → Prop} {l : List α} (h : Sorted r l) {a b : Fin l.length} (hab : a < b) :
r (l.get a) (l.get b)
source
theorem List.Sorted.rel_get_of_le{α : Type u} {r : α → α → Prop} [IsRefl α r] {l : List α} (h : Sorted r l) {a b : Fin l.length} (hab : a ≤ b) :
r (l.get a) (l.get b)
source
theorem List.Sorted.rel_of_mem_take_of_mem_drop{α : Type u} {r : α → α → Prop} {l : List α} (h : Sorted r l) {k : ℕ} {x y : α} (hx : x ∈ take k l) (hy : y ∈ drop k l) :
r x y
source
theorem List.Sorted.decide{α : Type u} {r : α → α → Prop} [DecidableRel r] (l : List α) (h : Sorted r l) :
Sorted (fun (a b : α) => Decidable.decide (r a b) = true) l
If a list is sorted with respect to a decidable relation, then it is sorted with respect to the corresponding Bool-valued relation.

source
theorem List.sorted_ofFn_iff{n : ℕ} {α : Type u} {f : Fin n → α} {r : α → α → Prop} :
Sorted r (ofFn f) ↔ Relator.LiftFun (fun (x1 x2 : Fin n) => x1 < x2) r f f
source
@[simp]
theorem List.sorted_lt_ofFn_iff{n : ℕ} {α : Type u} {f : Fin n → α} [Preorder α] :
Sorted (fun (x1 x2 : α) => x1 < x2) (ofFn f) ↔ StrictMono f
The list List.ofFn f is strictly sorted with respect to (· ≤ ·) if and only if f is strictly monotone.

source
@[simp]
theorem List.sorted_gt_ofFn_iff{n : ℕ} {α : Type u} {f : Fin n → α} [Preorder α] :
Sorted (fun (x1 x2 : α) => x1 > x2) (ofFn f) ↔ StrictAnti f
The list List.ofFn f is strictly sorted with respect to (· ≥ ·) if and only if f is strictly antitone.

source
@[simp]
theorem List.sorted_le_ofFn_iff{n : ℕ} {α : Type u} {f : Fin n → α} [Preorder α] :
Sorted (fun (x1 x2 : α) => x1 ≤ x2) (ofFn f) ↔ Monotone f
The list List.ofFn f is sorted with respect to (· ≤ ·) if and only if f is monotone.

source
theorem Monotone.ofFn_sorted{n : ℕ} {α : Type u} {f : Fin n → α} [Preorder α] :
Monotone f → List.Sorted (fun (x1 x2 : α) => x1 ≤ x2) (List.ofFn f)
The list obtained from a monotone tuple is sorted.

source
@[simp]
theorem List.sorted_ge_ofFn_iff{n : ℕ} {α : Type u} {f : Fin n → α} [Preorder α] :
Sorted (fun (x1 x2 : α) => x1 ≥ x2) (ofFn f) ↔ Antitone f
The list List.ofFn f is sorted with respect to (· ≥ ·) if and only if f is antitone.

source
theorem Antitone.ofFn_sorted{n : ℕ} {α : Type u} {f : Fin n → α} [Preorder α] :
Antitone f → List.Sorted (fun (x1 x2 : α) => x1 ≥ x2) (List.ofFn f)
The list obtained from an antitone tuple is sorted.

source
theorem List.Sorted.filterMap{α : Type u_1} {β : Type u_2} {p : α → Option β} {l : List α} {r : α → α → Prop} {r' : β → β → Prop} (hl : Sorted r l) (hp : ∀ (a b : α) (c d : β), p a = some c → p b = some d → r a b → r' c d) :
Sorted r' (List.filterMap p l)
source
@[simp]
theorem RelEmbedding.sorted_listMap{α : Type u_1} {β : Type u_2} {ra : α → α → Prop} {rb : β → β → Prop} (e : ra ↪r rb) {l : List α} :
List.Sorted rb (List.map (⇑e) l) ↔ List.Sorted ra l
source
@[simp]
theorem RelEmbedding.sorted_swap_listMap{α : Type u_1} {β : Type u_2} {ra : α → α → Prop} {rb : β → β → Prop} (e : ra ↪r rb) {l : List α} :
List.Sorted (Function.swap rb) (List.map (⇑e) l) ↔ List.Sorted (Function.swap ra) l
source
@[simp]
theorem OrderEmbedding.sorted_lt_listMap{α : Type u_1} {β : Type u_2} [Preorder α] [Preorder β] (e : α ↪o β) {l : List α} :
List.Sorted (fun (x1 x2 : β) => x1 < x2) (List.map (⇑e) l) ↔ List.Sorted (fun (x1 x2 : α) => x1 < x2) l
source
@[simp]
theorem OrderEmbedding.sorted_gt_listMap{α : Type u_1} {β : Type u_2} [Preorder α] [Preorder β] (e : α ↪o β) {l : List α} :
List.Sorted (fun (x1 x2 : β) => x1 > x2) (List.map (⇑e) l) ↔ List.Sorted (fun (x1 x2 : α) => x1 > x2) l
source
@[simp]
theorem RelIso.sorted_listMap{α : Type u_1} {β : Type u_2} {ra : α → α → Prop} {rb : β → β → Prop} (e : ra ≃r rb) {l : List α} :
List.Sorted rb (List.map (⇑e) l) ↔ List.Sorted ra l
source
@[simp]
theorem RelIso.sorted_swap_listMap{α : Type u_1} {β : Type u_2} {ra : α → α → Prop} {rb : β → β → Prop} (e : ra ≃r rb) {l : List α} :
List.Sorted (Function.swap rb) (List.map (⇑e) l) ↔ List.Sorted (Function.swap ra) l
source
@[simp]
theorem OrderIso.sorted_lt_listMap{α : Type u_1} {β : Type u_2} [Preorder α] [Preorder β] (e : α ≃o β) {l : List α} :
List.Sorted (fun (x1 x2 : β) => x1 < x2) (List.map (⇑e) l) ↔ List.Sorted (fun (x1 x2 : α) => x1 < x2) l
source
@[simp]
theorem OrderIso.sorted_gt_listMap{α : Type u_1} {β : Type u_2} [Preorder α] [Preorder β] (e : α ≃o β) {l : List α} :
List.Sorted (fun (x1 x2 : β) => x1 > x2) (List.map (⇑e) l) ↔ List.Sorted (fun (x1 x2 : α) => x1 > x2) l
source
theorem StrictMono.sorted_le_listMap{α : Type u_1} {β : Type u_2} [LinearOrder α] [Preorder β] {f : α → β} {l : List α} (hf : StrictMono f) :
List.Sorted (fun (x1 x2 : β) => x1 ≤ x2) (List.map f l) ↔ List.Sorted (fun (x1 x2 : α) => x1 ≤ x2) l
source
theorem StrictMono.sorted_ge_listMap{α : Type u_1} {β : Type u_2} [LinearOrder α] [Preorder β] {f : α → β} {l : List α} (hf : StrictMono f) :
List.Sorted (fun (x1 x2 : β) => x1 ≥ x2) (List.map f l) ↔ List.Sorted (fun (x1 x2 : α) => x1 ≥ x2) l
source
theorem StrictMono.sorted_lt_listMap{α : Type u_1} {β : Type u_2} [LinearOrder α] [Preorder β] {f : α → β} {l : List α} (hf : StrictMono f) :
List.Sorted (fun (x1 x2 : β) => x1 < x2) (List.map f l) ↔ List.Sorted (fun (x1 x2 : α) => x1 < x2) l
source
theorem StrictMono.sorted_gt_listMap{α : Type u_1} {β : Type u_2} [LinearOrder α] [Preorder β] {f : α → β} {l : List α} (hf : StrictMono f) :
List.Sorted (fun (x1 x2 : β) => x1 > x2) (List.map f l) ↔ List.Sorted (fun (x1 x2 : α) => x1 > x2) l
source
theorem StrictAnti.sorted_le_listMap{α : Type u_1} {β : Type u_2} [LinearOrder α] [Preorder β] {f : α → β} {l : List α} (hf : StrictAnti f) :
List.Sorted (fun (x1 x2 : β) => x1 ≤ x2) (List.map f l) ↔ List.Sorted (fun (x1 x2 : α) => x1 ≥ x2) l
source
theorem StrictAnti.sorted_ge_listMap{α : Type u_1} {β : Type u_2} [LinearOrder α] [Preorder β] {f : α → β} {l : List α} (hf : StrictAnti f) :
List.Sorted (fun (x1 x2 : β) => x1 ≥ x2) (List.map f l) ↔ List.Sorted (fun (x1 x2 : α) => x1 ≤ x2) l
source
theorem StrictAnti.sorted_lt_listMap{α : Type u_1} {β : Type u_2} [LinearOrder α] [Preorder β] {f : α → β} {l : List α} (hf : StrictAnti f) :
List.Sorted (fun (x1 x2 : β) => x1 < x2) (List.map f l) ↔ List.Sorted (fun (x1 x2 : α) => x1 > x2) l
source
theorem StrictAnti.sorted_gt_listMap{α : Type u_1} {β : Type u_2} [LinearOrder α] [Preorder β] {f : α → β} {l : List α} (hf : StrictAnti f) :
List.Sorted (fun (x1 x2 : β) => x1 > x2) (List.map f l) ↔ List.Sorted (fun (x1 x2 : α) => x1 < x2) l
Insertion sort 
source
def List.orderedInsert{α : Type u} (r : α → α → Prop) [DecidableRel r] (a : α) :
List α → List α
orderedInsert a l inserts a into l at such that orderedInsert a l is sorted if l is.

Equations
source
theorem List.orderedInsert_of_le{α : Type u} (r : α → α → Prop) [DecidableRel r] {a b : α} (l : List α) (h : r a b) :
orderedInsert r a (b :: l) = a :: b :: l
source
def List.insertionSort{α : Type u} (r : α → α → Prop) [DecidableRel r] :
List α → List α
insertionSort l returns l sorted using the insertion sort algorithm.

Equations
source
@[simp]
theorem List.orderedInsert_nil{α : Type u} (r : α → α → Prop) [DecidableRel r] (a : α) :
orderedInsert r a [] = [a]
source
theorem List.orderedInsert_length{α : Type u} (r : α → α → Prop) [DecidableRel r] (L : List α) (a : α) :
(orderedInsert r a L).length = L.length + 1
source
theorem List.orderedInsert_eq_take_drop{α : Type u} (r : α → α → Prop) [DecidableRel r] (a : α) (l : List α) :
orderedInsert r a l = takeWhile (fun (b : α) => decide ¬r a b) l ++ a :: dropWhile (fun (b : α) => decide ¬r a b) l
An alternative definition of orderedInsert using takeWhile and dropWhile.

source
theorem List.insertionSort_cons_eq_take_drop{α : Type u} (r : α → α → Prop) [DecidableRel r] (a : α) (l : List α) :
insertionSort r (a :: l) = takeWhile (fun (b : α) => decide ¬r a b) (insertionSort r l) ++ a :: dropWhile (fun (b : α) => decide ¬r a b) (insertionSort r l)
source
@[simp]
theorem List.mem_orderedInsert{α : Type u} (r : α → α → Prop) [DecidableRel r] {a b : α} {l : List α} :
a ∈ orderedInsert r b l ↔ a = b ∨ a ∈ l
source
theorem List.map_orderedInsert{α : Type u} {β : Type v} (r : α → α → Prop) (s : β → β → Prop) [DecidableRel r] [DecidableRel s] (f : α → β) (l : List α) (x : α) (hl₁ : ∀ a ∈ l, r a x ↔ s (f a) (f x)) (hl₂ : ∀ a ∈ l, r x a ↔ s (f x) (f a)) :
map f (orderedInsert r x l) = orderedInsert s (f x) (map f l)
source
theorem List.perm_orderedInsert{α : Type u} (r : α → α → Prop) [DecidableRel r] (a : α) (l : List α) :
(orderedInsert r a l).Perm (a :: l)
source
theorem List.orderedInsert_count{α : Type u} (r : α → α → Prop) [DecidableRel r] [DecidableEq α] (L : List α) (a b : α) :
count a (orderedInsert r b L) = count a L + if b = a then 1 else 0
source
theorem List.perm_insertionSort{α : Type u} (r : α → α → Prop) [DecidableRel r] (l : List α) :
(insertionSort r l).Perm l
source
@[simp]
theorem List.mem_insertionSort{α : Type u} (r : α → α → Prop) [DecidableRel r] {l : List α} {x : α} :
x ∈ insertionSort r l ↔ x ∈ l
source
@[simp]
theorem List.length_insertionSort{α : Type u} (r : α → α → Prop) [DecidableRel r] (l : List α) :
(insertionSort r l).length = l.length
source
theorem List.insertionSort_cons{α : Type u} (r : α → α → Prop) [DecidableRel r] {a : α} {l : List α} (h : ∀ b ∈ l, r a b) :
insertionSort r (a :: l) = a :: insertionSort r l
source
theorem List.map_insertionSort{α : Type u} {β : Type v} (r : α → α → Prop) (s : β → β → Prop) [DecidableRel r] [DecidableRel s] (f : α → β) (l : List α) (hl : ∀ a ∈ l, ∀ b ∈ l, r a b ↔ s (f a) (f b)) :
map f (insertionSort r l) = insertionSort s (map f l)
source
theorem List.Sorted.insertionSort_eq{α : Type u} {r : α → α → Prop} [DecidableRel r] {l : List α} :
Sorted r l → insertionSort r l = l
If l is already List.Sorted with respect to r, then insertionSort does not change it.

source
theorem List.erase_orderedInsert{α : Type u} {r : α → α → Prop} [DecidableRel r] [DecidableEq α] [IsRefl α r] (x : α) (xs : List α) :
(orderedInsert r x xs).erase x = xs
For a reflexive relation, insert then erasing is the identity.

source
theorem List.erase_orderedInsert_of_notMem{α : Type u} {r : α → α → Prop} [DecidableRel r] [DecidableEq α] {x : α} {xs : List α} (hx : x ∉ xs) :
(orderedInsert r x xs).erase x = xs
Inserting then erasing an element that is absent is the identity.

source
@[deprecated List.erase_orderedInsert_of_notMem (since := "2025-05-23")]
theorem List.erase_orderedInsert_of_not_mem{α : Type u} {r : α → α → Prop} [DecidableRel r] [DecidableEq α] {x : α} {xs : List α} (hx : x ∉ xs) :
(orderedInsert r x xs).erase x = xs
Alias of List.erase_orderedInsert_of_notMem.

Inserting then erasing an element that is absent is the identity.

source
theorem List.orderedInsert_erase{α : Type u} {r : α → α → Prop} [DecidableRel r] [DecidableEq α] [IsAntisymm α r] (x : α) (xs : List α) (hx : x ∈ xs) (hxs : Sorted r xs) :
orderedInsert r x (xs.erase x) = xs
For an antisymmetric relation, erasing then inserting is the identity.

source
theorem List.sublist_orderedInsert{α : Type u} {r : α → α → Prop} [DecidableRel r] (x : α) (xs : List α) :
xs.Sublist (orderedInsert r x xs)
source
theorem List.cons_sublist_orderedInsert{α : Type u} {r : α → α → Prop} [DecidableRel r] {l c : List α} {a : α} (hl : c.Sublist l) (ha : ∀ a' ∈ c, r a a') :
(a :: c).Sublist (orderedInsert r a l)
source
theorem List.Sublist.orderedInsert_sublist{α : Type u} {r : α → α → Prop} [DecidableRel r] [IsTrans α r] {as bs : List α} (x : α) (hs : as.Sublist bs) (hb : Sorted r bs) :
(orderedInsert r x as).Sublist (orderedInsert r x bs)
source
theorem List.Sorted.orderedInsert{α : Type u} {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r] (a : α) (l : List α) :
Sorted r l → Sorted r (List.orderedInsert r a l)
source
theorem List.sorted_insertionSort{α : Type u} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] (l : List α) :
Sorted r (insertionSort r l)
The list List.insertionSort r l is List.Sorted with respect to r.

source
theorem List.sublist_insertionSort{α : Type u} {r : α → α → Prop} [DecidableRel r] {l c : List α} (hr : Pairwise r c) (hc : c.Sublist l) :
c.Sublist (insertionSort r l)
If c is a sorted sublist of l, then c is still a sublist of insertionSort r l.

source
theorem List.pair_sublist_insertionSort{α : Type u} {r : α → α → Prop} [DecidableRel r] {a b : α} {l : List α} (hab : r a b) (h : [a, b].Sublist l) :
[a, b].Sublist (insertionSort r l)
Another statement of stability of insertion sort. If a pair [a, b] is a sublist of l and r a b, then [a, b] is still a sublist of insertionSort r l.

source
theorem List.sublist_insertionSort'{α : Type u} {r : α → α → Prop} [DecidableRel r] [IsAntisymm α r] [IsTotal α r] [IsTrans α r] {l c : List α} (hs : Sorted r c) (hc : c.Subperm l) :
c.Sublist (insertionSort r l)
A version of insertionSort_stable which only assumes c <+~ l (instead of c <+ l), but additionally requires IsAntisymm α r, IsTotal α r and IsTrans α r.

source
theorem List.pair_sublist_insertionSort'{α : Type u} {r : α → α → Prop} [DecidableRel r] [IsAntisymm α r] [IsTotal α r] [IsTrans α r] {a b : α} {l : List α} (hab : r a b) (h : [a, b].Subperm l) :
[a, b].Sublist (insertionSort r l)
Another statement of stability of insertion sort. If a pair [a, b] is a sublist of a permutation of l and a ≼ b, then [a, b] is still a sublist of insertionSort r l.

Merge sort 
We provide some wrapper functions around the theorems for mergeSort provided in Lean, which rather than using explicit hypotheses for transitivity and totality, use Mathlib order typeclasses instead.

source
theorem List.Sorted.merge{α : Type u} {r : α → α → Prop} [DecidableRel r] [IsTotal α r] [IsTrans α r] {l l' : List α} (h : Sorted r l) (h' : Sorted r l') :
Sorted r (l.merge l' fun (x1 x2 : α) => Decidable.decide (r x1 x2))
source
theorem List.sorted_mergeSort'{α : Type u} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] (l : List α) :
Sorted r (l.mergeSort fun (x1 x2 : α) => decide (r x1 x2))
Variant of sorted_mergeSort using relation typeclasses.

source
theorem List.mergeSort_eq_self{α : Type u} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] [IsAntisymm α r] {l : List α} :
Sorted r l → (l.mergeSort fun (x1 x2 : α) => decide (r x1 x2)) = l
source
theorem List.mergeSort_eq_insertionSort{α : Type u} (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r] [IsAntisymm α r] (l : List α) :
(l.mergeSort fun (x1 x2 : α) => decide (r x1 x2)) = insertionSort r l

Basic properties of mergeSort. 
sorted_mergeSort: mergeSort produces a sorted list.
mergeSort_perm: mergeSort is a permutation of the input list.
mergeSort_of_sorted: mergeSort does not change a sorted list.
mergeSort_cons: proves mergeSort le (x :: xs) = l₁ ++ x :: l₂ for some l₁, l₂ so that mergeSort le xs = l₁ ++ l₂, and no a ∈ l₁ satisfies le a x.
sublist_mergeSort: if c is a sorted sublist of l, then c is still a sublist of mergeSort le l.
splitInTwo 
source
@[simp]
theorem List.MergeSort.Internal.splitInTwo_fst{α : Type u_1} {n : Nat} (l : { l : List α // l.length = n }) :
(splitInTwo l).fst = ⟨take ((n + 1) / 2) l.val, ⋯⟩
source
@[simp]
theorem List.MergeSort.Internal.splitInTwo_snd{α : Type u_1} {n : Nat} (l : { l : List α // l.length = n }) :
(splitInTwo l).snd = ⟨drop ((n + 1) / 2) l.val, ⋯⟩
source
theorem List.MergeSort.Internal.splitInTwo_fst_append_splitInTwo_snd{α : Type u_1} {n : Nat} (l : { l : List α // l.length = n }) :
(splitInTwo l).fst.val ++ (splitInTwo l).snd.val = l.val
source
theorem List.MergeSort.Internal.splitInTwo_cons_cons_zipIdx_fst{α : Type u_1} {a b : α} (i : Nat) (l : List α) :
(splitInTwo ⟨(a, i) :: (b, i + 1) :: l.zipIdx (i + 2), ⋯⟩).fst.val = (splitInTwo ⟨a :: b :: l, ⋯⟩).fst.val.zipIdx i
source
theorem List.MergeSort.Internal.splitInTwo_cons_cons_zipIdx_snd{α : Type u_1} {a b : α} (i : Nat) (l : List α) :
(splitInTwo ⟨(a, i) :: (b, i + 1) :: l.zipIdx (i + 2), ⋯⟩).snd.val = (splitInTwo ⟨a :: b :: l, ⋯⟩).snd.val.zipIdx (i + (l.length + 3) / 2)
source
theorem List.MergeSort.Internal.splitInTwo_fst_sorted{α : Type u_1} {n : Nat} {le : α → α → Prop} (l : { l : List α // l.length = n }) (h : Pairwise le l.val) :
Pairwise le (splitInTwo l).fst.val
source
theorem List.MergeSort.Internal.splitInTwo_snd_sorted{α : Type u_1} {n : Nat} {le : α → α → Prop} (l : { l : List α // l.length = n }) (h : Pairwise le l.val) :
Pairwise le (splitInTwo l).snd.val
source
theorem List.MergeSort.Internal.splitInTwo_fst_le_splitInTwo_snd{α : Type u_1} {n : Nat} {le : α → α → Prop} {l : { l : List α // l.length = n }} (h : Pairwise le l.val) (a b : α) :
a ∈ (splitInTwo l).fst.val → b ∈ (splitInTwo l).snd.val → le a b
zipIdxLE 
source
theorem List.zipIdxLE_trans{α : Type u_1} {le : α → α → Bool} (trans : ∀ (a b c : α), le a b = true → le b c = true → le a c = true) (a b c : α × Nat) :
zipIdxLE le a b = true → zipIdxLE le b c = true → zipIdxLE le a c = true
source
theorem List.zipIdxLE_total{α : Type u_1} {le : α → α → Bool} (total : ∀ (a b : α), (le a b || le b a) = true) (a b : α × Nat) :
(zipIdxLE le a b || zipIdxLE le b a) = true
merge 
source
theorem List.cons_merge_cons{α : Type u_1} (s : α → α → Bool) (a b : α) (l r : List α) :
(a :: l).merge (b :: r) s = if s a b = true then a :: l.merge (b :: r) s else b :: (a :: l).merge r s
source
@[simp]
theorem List.cons_merge_cons_pos{α : Type u_1} {a b : α} (s : α → α → Bool) (l r : List α) (h : s a b = true) :
(a :: l).merge (b :: r) s = a :: l.merge (b :: r) s
source
@[simp]
theorem List.cons_merge_cons_neg{α : Type u_1} {a b : α} (s : α → α → Bool) (l r : List α) (h : ¬s a b = true) :
(a :: l).merge (b :: r) s = b :: (a :: l).merge r s
source
@[simp, irreducible]
theorem List.length_merge{α : Type u_1} (s : α → α → Bool) (l r : List α) :
(l.merge r s).length = l.length + r.length
source
theorem List.mem_merge{α : Type u_1} {le : α → α → Bool} {a : α} {xs ys : List α} :
a ∈ xs.merge ys le ↔ a ∈ xs ∨ a ∈ ys
The elements of merge le xs ys are exactly the elements of xs and ys.

source
theorem List.mem_merge_left{α : Type u_1} {l : List α} {x : α} {r : List α} (s : α → α → Bool) (h : x ∈ l) :
x ∈ l.merge r s
source
theorem List.mem_merge_right{α : Type u_1} {r : List α} {x : α} {l : List α} (s : α → α → Bool) (h : x ∈ r) :
x ∈ l.merge r s
source
@[irreducible]
theorem List.merge_stable{α : Type u_1} {le : α → α → Bool} (xs ys : List (α × Nat)) :
(∀ (x y : α × Nat), x ∈ xs → y ∈ ys → x.snd ≤ y.snd) →
  map (fun (x : α × Nat) => x.fst) (xs.merge ys (zipIdxLE le)) =     (map (fun (x : α × Nat) => x.fst) xs).merge (map (fun (x : α × Nat) => x.fst) ys) le
source
theorem List.sorted_merge{α : Type u_1} {le : α → α → Bool} (trans : ∀ (a b c : α), le a b = true → le b c = true → le a c = true) (total : ∀ (a b : α), (le a b || le b a) = true) (l₁ l₂ : List α) (h₁ : Pairwise (fun (a b : α) => le a b = true) l₁) (h₂ : Pairwise (fun (a b : α) => le a b = true) l₂) :
Pairwise (fun (a b : α) => le a b = true) (l₁.merge l₂ le)
If the ordering relation le is transitive and total (i.e. le a b || le b a for all a, b) then the merge of two sorted lists is sorted.

source
theorem List.merge_of_le{α : Type u_1} {le : α → α → Bool} {xs ys : List α} :
(∀ (a b : α), a ∈ xs → b ∈ ys → le a b = true) → xs.merge ys le = xs ++ ys
source
@[irreducible]
theorem List.merge_perm_append{α : Type u_1} (le : α → α → Bool) {xs ys : List α} :
(xs.merge ys le).Perm (xs ++ ys)
source
theorem List.Perm.merge{α : Type u_1} {l₁ l₂ r₁ r₂ : List α} (s₁ s₂ : α → α → Bool) (hl : l₁.Perm l₂) (hr : r₁.Perm r₂) :
(l₁.merge r₁ s₁).Perm (l₂.merge r₂ s₂)
mergeSort 
source
@[simp]
theorem List.mergeSort_nil{α✝ : Type u_1} {r : α✝ → α✝ → Bool} :
[].mergeSort r = []
source
@[simp]
theorem List.mergeSort_singleton{α : Type u_1} {r : α → α → Bool} (a : α) :
[a].mergeSort r = [a]
source
@[irreducible]
theorem List.mergeSort_perm{α : Type u_1} (l : List α) (le : α → α → Bool) :
(l.mergeSort le).Perm l
source
@[simp]
theorem List.length_mergeSort{α : Type u_1} {le : α → α → Bool} (l : List α) :
(l.mergeSort le).length = l.length
source
@[simp]
theorem List.mem_mergeSort{α : Type u_1} {le : α → α → Bool} {a : α} {l : List α} :
a ∈ l.mergeSort le ↔ a ∈ l
source
@[irreducible]
theorem List.sorted_mergeSort{α : Type u_1} {le : α → α → Bool} (trans : ∀ (a b c : α), le a b = true → le b c = true → le a c = true) (total : ∀ (a b : α), (le a b || le b a) = true) (l : List α) :
Pairwise (fun (a b : α) => le a b = true) (l.mergeSort le)
The result of mergeSort is sorted, as long as the comparison function is transitive (le a b → le b c → le a c) and total in the sense that le a b || le b a.

The comparison function need not be irreflexive, i.e. le a b and le b a is allowed even when a ≠ b.

source
@[irreducible]
theorem List.mergeSort_of_sorted{α : Type u_1} {le : α → α → Bool} {l : List α} :
Pairwise (fun (a b : α) => le a b = true) l → l.mergeSort le = l
If the input list is already sorted, then mergeSort does not change the list.

source
theorem List.mergeSort_zipIdx{α : Type u_1} {le : α → α → Bool} {l : List α} :
map (fun (x : α × Nat) => x.fst) (l.zipIdx.mergeSort (zipIdxLE le)) = l.mergeSort le
This merge sort algorithm is stable, in the sense that breaking ties in the ordering function using the position in the list has no effect on the output.

That is, elements which are equal with respect to the ordering function will remain in the same order in the output list as they were in the input list.

See also:

sublist_mergeSort: if c <+ l and c.Pairwise le, then c <+ mergeSort le l.
pair_sublist_mergeSort: if [a, b] <+ l and le a b, then [a, b] <+ mergeSort le l)
source
@[irreducible]
theorem List.mergeSort_zipIdx.go{α : Type u_1} {le : α → α → Bool} (i : Nat) (l : List α) :
map (fun (x : α × Nat) => x.fst) ((l.zipIdx i).mergeSort (zipIdxLE le)) = l.mergeSort le
source
@[reducible, inline, deprecated List.mergeSort_zipIdx (since := "2025-01-21")]
abbrev List.mergeSort_enum{α : Type u_1} {le : α → α → Bool} {l : List α} :
map (fun (x : α × Nat) => x.fst) (l.zipIdx.mergeSort (zipIdxLE le)) = l.mergeSort le
Equations
source
theorem List.mergeSort_cons{α : Type u_1} {le : α → α → Bool} (trans : ∀ (a b c : α), le a b = true → le b c = true → le a c = true) (total : ∀ (a b : α), (le a b || le b a) = true) (a : α) (l : List α) :
∃ (l₁ : List α), ∃ (l₂ : List α), (a :: l).mergeSort le = l₁ ++ a :: l₂ ∧ l.mergeSort le = l₁ ++ l₂ ∧ ∀ (b : α), b ∈ l₁ → (!le a b) = true
source
theorem List.sublist_mergeSort{α : Type u_1} {le : α → α → Bool} {xs : List α} (trans : ∀ (a b c : α), le a b = true → le b c = true → le a c = true) (total : ∀ (a b : α), (le a b || le b a) = true) {ys : List α} :
Pairwise (fun (a b : α) => le a b = true) ys → ys.Sublist xs → ys.Sublist (xs.mergeSort le)
Another statement of stability of merge sort. If c is a sorted sublist of l, then c is still a sublist of mergeSort le l.

source
theorem List.pair_sublist_mergeSort{α : Type u_1} {le : α → α → Bool} {a b : α} {l : List α} (trans : ∀ (a b c : α), le a b = true → le b c = true → le a c = true) (total : ∀ (a b : α), (le a b || le b a) = true) (hab : le a b = true) (h : [a, b].Sublist l) :
[a, b].Sublist (l.mergeSort le)
Another statement of stability of merge sort. If a pair [a, b] is a sublist of l and le a b, then [a, b] is still a sublist of mergeSort le l.

source
@[irreducible]
theorem List.map_merge{α : Type u_2} {β : Type u_1} {f : α → β} {r : α → α → Bool} {s : β → β → Bool} {l l' : List α} (hl : ∀ (a : α), a ∈ l → ∀ (b : α), b ∈ l' → r a b = s (f a) (f b)) :
map f (l.merge l' r) = (map f l).merge (map f l') s
source
@[irreducible]
theorem List.map_mergeSort{α : Type u_2} {β : Type u_1} {r : α → α → Bool} {s : β → β → Bool} {f : α → β} {l : List α} (hl : ∀ (a : α), a ∈ l → ∀ (b : α), b ∈ l → r a b = s (f a) (f b)) :
map f (l.mergeSort r) = (map f l).mergeSort s


List Permutations
Perm
source
inductive List.Perm{α : Type u} :
List α → List α → Prop
Two lists are permutations of each other if they contain the same elements, each occurring the same number of times but not necessarily in the same order.
One list can be proven to be a permutation of another by showing how to transform one into the other by repeatedly swapping adjacent elements.
List.isPerm is a Boolean equivalent of this relation.
nil {α : Type u} : [].Perm []
The empty list is a permutation of the empty list: [] ~ [].
cons {α : Type u} (x : α) {l₁ l₂ : List α} : l₁.Perm l₂ → (x :: l₁).Perm (x :: l₂)
If one list is a permutation of the other, adding the same element as the head of each yields lists that are permutations of each other: l₁ ~ l₂ → x::l₁ ~ x::l₂.
swap {α : Type u} (x y : α) (l : List α) : (y :: x :: l).Perm (x :: y :: l)
If two lists are identical except for having their first two elements swapped, then they are permutations of each other: x::y::l ~ y::x::l.
trans {α : Type u} {l₁ l₂ l₃ : List α} : l₁.Perm l₂ → l₂.Perm l₃ → l₁.Perm l₃
Permutation is transitive: l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃.
Instances For
source
def List.«term_~_»:
Lean.TrailingParserDescr
Two lists are permutations of each other if they contain the same elements, each occurring the same number of times but not necessarily in the same order.
One list can be proven to be a permutation of another by showing how to transform one into the other by repeatedly swapping adjacent elements.
List.isPerm is a Boolean equivalent of this relation.
Equations
isPerm
source
def List.isPerm{α : Type u} [BEq α] :
List α → List α → Bool
Returns true if l₁ and l₂ are permutations of each other. O(|l₁| * |l₂|).
The relation List.Perm is a logical characterization of permutations. When the BEq α instance corresponds to DecidableEq α, isPerm l₁ l₂ ↔ l₁ ~ l₂ (use the theorem isPerm_iff).
Equations
Logical operations
any
source
def List.any{α : Type u} (l : List α) (p : α → Bool) :
Bool
Returns true if p returns true for any element of l.
O(|l|). Short-circuits upon encountering the first true.
Examples:
[2, 4, 6].any (· % 2 = 0) = true
[2, 4, 6].any (· % 2 = 1) = false
[2, 4, 5, 6].any (· % 2 = 0) = true
[2, 4, 5, 6].any (· % 2 = 1) = true
Equations
source
@[simp]
theorem List.any_nil{α✝ : Type u_1} {f : α✝ → Bool} :
[].any f = false
source
@[simp]
theorem List.any_cons{α✝ : Type u_1} {a : α✝} {l : List α✝} {f : α✝ → Bool} :
(a :: l).any f = (f a || l.any f)
all
source
def List.all{α : Type u} :
List α → (α → Bool) → Bool
Returns true if p returns true for every element of l.
O(|l|). Short-circuits upon encountering the first false.
Examples:
[a, b, c].all p = (p a && (p b && p c))
[2, 4, 6].all (· % 2 = 0) = true
[2, 4, 5, 6].all (· % 2 = 0) = false
Equations
source
@[simp]
theorem List.all_nil{α✝ : Type u_1} {f : α✝ → Bool} :
[].all f = true
source
@[simp]
theorem List.all_cons{α✝ : Type u_1} {a : α✝} {l : List α✝} {f : α✝ → Bool} :
(a :: l).all f = (f a && l.all f)
or
source
def List.or(bs : List Bool) :
Bool
Returns true if true is an element of the list bs.
O(|bs|). Short-circuits at the first true value.
[true, true, true].or = true
[true, false, true].or = true
[false, false, false].or = false
[false, false, true].or = true
[].or = false
Equations
source
@[simp]
theorem List.or_nil:
[].or = false
source
@[simp]
theorem List.or_cons{a : Bool} {l : List Bool} :
(a :: l).or = (a || l.or)
and
source
def List.and(bs : List Bool) :
Bool
Returns true if every element of bs is the value true.
O(|bs|). Short-circuits at the first false value.
[true, true, true].and = true
[true, false, true].and = false
[true, false, false].and = false
[].and = true
Equations
source
@[simp]
theorem List.and_nil:
[].and = true
source
@[simp]
theorem List.and_cons{a : Bool} {l : List Bool} :
(a :: l).and = (a && l.and)
Zippers
zipWith
source
@[specialize #[]]
def List.zipWith{α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (xs : List α) (ys : List β) :
List γ
Applies a function to the corresponding elements of two lists, stopping at the end of the shorter list.
O(min |xs| |ys|).
Examples:
[1, 2].zipWith (· + ·) [5, 6] = [6, 8]
[1, 2, 3].zipWith (· + ·) [5, 6, 10] = [6, 8, 13]
[].zipWith (· + ·) [5, 6] = []
[x₁, x₂, x₃].zipWith f [y₁, y₂, y₃, y₄] = [f x₁ y₁, f x₂ y₂, f x₃ y₃]
Equations
Instances For
source
@[simp]
theorem List.zipWith_nil_left{α : Type u} {β : Type v} {γ : Type w} {l : List β} {f : α → β → γ} :
zipWith f [] l = []
source
@[simp]
theorem List.zipWith_nil_right{α : Type u} {β : Type v} {γ : Type w} {l : List α} {f : α → β → γ} :
zipWith f l [] = []
source
@[simp]
theorem List.zipWith_cons_cons{α : Type u} {β : Type v} {γ : Type w} {a : α} {as : List α} {b : β} {bs : List β} {f : α → β → γ} :
zipWith f (a :: as) (b :: bs) = f a b :: zipWith f as bs
zip
source
def List.zip{α : Type u} {β : Type v} :
List α → List β → List (α × β)
Combines two lists into a list of pairs in which the first and second components are the corresponding elements of each list. The resulting list is the length of the shorter of the input lists.
O(min |xs| |ys|).
Examples:
["Mon", "Tue", "Wed"].zip [1, 2, 3] = [("Mon", 1), ("Tue", 2), ("Wed", 3)]
["Mon", "Tue", "Wed"].zip [1, 2] = [("Mon", 1), ("Tue", 2)]
[x₁, x₂, x₃].zip [y₁, y₂, y₃, y₄] = [(x₁, y₁), (x₂, y₂), (x₃, y₃)]
Equations
source
@[simp]
theorem List.zip_nil_left{α : Type u} {β : Type v} {l : List β} :
[].zip l = []
source
@[simp]
theorem List.zip_nil_right{α : Type u} {β : Type v} {l : List α} :
l.zip [] = []
source
@[simp]
theorem List.zip_cons_cons{α✝ : Type u_1} {a : α✝} {as : List α✝} {α✝¹ : Type u_2} {b : α✝¹} {bs : List α✝¹} :
(a :: as).zip (b :: bs) = (a, b) :: as.zip bs
zipWithAll
source
def List.zipWithAll{α : Type u} {β : Type v} {γ : Type w} (f : Option α → Option β → γ) :
List α → List β → List γ
Applies a function to the corresponding elements of both lists, stopping when there are no more elements in either list. If one list is shorter than the other, the function is passed none for the missing elements.
Examples:
[1, 6].zipWithAll min [5, 2] = [some 1, some 2]
[1, 2, 3].zipWithAll Prod.mk [5, 6] = [(some 1, some 5), (some 2, some 6), (some 3, none)]
[x₁, x₂].zipWithAll f [y] = [f (some x₁) (some y), f (some x₂) none]
Equations
source
@[simp]
theorem List.zipWithAll_nil{α✝ : Type u_1} {α✝¹ : Type u_2} {α✝² : Type u_3} {f : Option α✝ → Option α✝¹ → α✝²} {as : List α✝} :
zipWithAll f as [] = map (fun (a : α✝) => f (some a) none) as
source
@[simp]
theorem List.nil_zipWithAll{α✝ : Type u_1} {α✝¹ : Type u_2} {α✝² : Type u_3} {f : Option α✝ → Option α✝¹ → α✝²} {bs : List α✝¹} :
zipWithAll f [] bs = map (fun (b : α✝¹) => f none (some b)) bs
source
@[simp]
theorem List.zipWithAll_cons_cons{α✝ : Type u_1} {α✝¹ : Type u_2} {α✝² : Type u_3} {f : Option α✝ → Option α✝¹ → α✝²} {a : α✝} {as : List α✝} {b : α✝¹} {bs : List α✝¹} :
zipWithAll f (a :: as) (b :: bs) = f (some a) (some b) :: zipWithAll f as bs
unzip
source
def List.unzip{α : Type u} {β : Type v} (l : List (α × β)) :
List α × List β
Separates a list of pairs into two lists that contain the respective first and second components.
O(|l|).
Examples:
[("Monday", 1), ("Tuesday", 2)].unzip = (["Monday", "Tuesday"], [1, 2])
[(x₁, y₁), (x₂, y₂), (x₃, y₃)].unzip = ([x₁, x₂, x₃], [y₁, y₂, y₃])
([] : List (Nat × String)).unzip = (([], []) : List Nat × List String)
Equations
source
@[simp]
theorem List.unzip_nil{α : Type u} {β : Type v} :
[].unzip = ([], [])
source
@[simp]
theorem List.unzip_cons{α : Type u} {β : Type v} {t : List (α × β)} {h : α × β} :
(h :: t).unzip = match t.unzip with
| (as, bs) => (h.fst :: as, h.snd :: bs)
Ranges and enumeration
source
def List.sum{α : Type u_1} [Add α] [Zero α] :
List α → α
Computes the sum of the elements of a list.
Examples:
[a, b, c].sum = a + (b + (c + 0))
[1, 2, 5].sum = 8
Equations
source
@[simp]
theorem List.sum_nil{α : Type u} [Add α] [Zero α] :
[].sum = 0
source
@[simp]
theorem List.sum_cons{α : Type u} [Add α] [Zero α] {a : α} {l : List α} :
(a :: l).sum = a + l.sum
range
source
def List.range(n : Nat) :
List Nat
Returns a list of the numbers from 0 to n exclusive, in increasing order.
O(n).
Examples:
range 5 = [0, 1, 2, 3, 4]
range 0 = []
range 2 = [0, 1]
Equations
source
def List.range.loop:
Nat → List Nat → List Nat
Equations
source
@[simp]
theorem List.range_zero:
range 0 = []
range'
source
def List.range'(start len : Nat) (step : Nat := 1) :
List Nat
Returns a list of the numbers with the given length len, starting at start and increasing by step at each element.
In other words, List.range' start len step is [start, start+step, ..., start+(len-1)*step].
Examples:
List.range' 0 3 (step := 1) = [0, 1, 2]
List.range' 0 3 (step := 2) = [0, 2, 4]
List.range' 0 4 (step := 2) = [0, 2, 4, 6]
List.range' 3 4 (step := 2) = [3, 5, 7, 9]
Equations
iota
source
@[deprecated "Use (List.range' 1 n).reverse instead of iota n." (since := "2025-01-20")]
def List.iota:
Nat → List Nat
O(n). iota n is the numbers from 1 to n inclusive, in decreasing order.
iota 5 = [5, 4, 3, 2, 1]
Equations
source
@[simp]
theorem List.iota_zero:
iota 0 = []
source
@[simp]
theorem List.iota_succ{i : Nat} :
iota (i + 1) = (i + 1) :: iota i
zipIdx
source
def List.zipIdx{α : Type u} (l : List α) (n : Nat := 0) :
List (α × Nat)
Pairs each element of a list with its index, optionally starting from an index other than 0.
O(|l|).
Examples:
[a, b, c].zipIdx = [(a, 0), (b, 1), (c, 2)]
[a, b, c].zipIdx 5 = [(a, 5), (b, 6), (c, 7)]
Equations
source
@[simp]
theorem List.zipIdx_nil{α : Type u} {i : Nat} :
[].zipIdx i = []
source
@[simp]
theorem List.zipIdx_cons{α✝ : Type u_1} {a : α✝} {as : List α✝} {i : Nat} :
(a :: as).zipIdx i = (a, i) :: as.zipIdx (i + 1)
enumFrom
source
@[deprecated "Use zipIdx instead; note the signature change." (since := "2025-01-21")]
def List.enumFrom{α : Type u} :
Nat → List α → List (Nat × α)
O(|l|). enumFrom n l is like enum but it allows you to specify the initial index.
enumFrom 5 [a, b, c] = [(5, a), (6, b), (7, c)]
Equations
source
@[simp, deprecated List.zipIdx_nil (since := "2025-01-21")]
theorem List.enumFrom_nil{α : Type u} {i : Nat} :
enumFrom i [] = []
source
@[simp, deprecated List.zipIdx_cons (since := "2025-01-21")]
theorem List.enumFrom_cons{α✝ : Type u_1} {a : α✝} {as : List α✝} {i : Nat} :
enumFrom i (a :: as) = (i, a) :: enumFrom (i + 1) as
enum
source
@[deprecated "Use zipIdx instead; note the signature change." (since := "2025-01-21")]
def List.enum{α : Type u} :
List α → List (Nat × α)
O(|l|). enum l pairs up each element with its index in the list.
enum [a, b, c] = [(0, a), (1, b), (2, c)]
Equations
source
@[simp, deprecated List.zipIdx_nil (since := "2025-01-21")]
theorem List.enum_nil{α : Type u} :
[].enum = []


List.length_nil
List.length_singleton
List.length_cons
List.length_set
List.foldl_nil
List.foldl_cons
List.length_concat
List.of_concat_eq_concat
List.beq
List.beq_nil_nil
List.beq_cons_nil
List.beq_nil_cons
List.beq_cons₂
List.instBEq
List.instReflBEq
List.instLawfulBEq
List.isEqv
List.isEqv_nil_nil
List.isEqv_nil_cons
List.isEqv_cons_nil
List.isEqv_cons₂
List.Lex
List.decidableLex
List.lt
List.instLT
List.decidableLT
List.hasDecidableLt
List.le
List.instLE
List.decidableLE
List.lex
List.nil_lex_nil
List.nil_lex_cons
List.cons_lex_nil
List.cons_lex_cons
List.lex_nil
List.lex_nil_nil
List.lex_nil_cons
List.lex_cons_nil
List.lex_cons_cons
List.getLast
List.getLast?
List.getLast?_nil
List.getLastD
List.getLastD_nil
List.getLastD_cons
List.head
List.head_cons
List.head?
List.head?_nil
List.head?_cons
List.headD
List.headD_nil
List.headD_cons
List.tail
List.tail_nil
List.tail_cons
List.tail?
List.tail?_nil
List.tail?_cons
List.tailD
List.tailD_nil
List.tailD_cons
List.map
List.map_nil
List.map_cons
List.filter
List.filter_nil
List.filterMap
List.filterMap_nil
List.filterMap_cons
List.foldr
List.foldr_nil
List.foldr_cons
List.reverseAux
List.reverseAux_nil
List.reverseAux_cons
List.reverse
List.reverse_nil
List.reverseAux_reverseAux
List.append
List.appendTR
List.append_eq_appendTR
List.instAppend
List.append_eq
List.nil_append
List.cons_append
List.append_nil
List.instLawfulIdentityHAppendNil
List.length_append
List.append_assoc
List.instAssociativeHAppend
List.append_cons
List.concat_eq_append
List.reverseAux_eq_append
List.reverse_cons
List.flatten
List.flatten_nil
List.flatten_cons
List.singleton
List.flatMap
List.flatMap_nil
List.flatMap_cons
List.replicate
List.replicate_zero
List.replicate_succ
List.length_replicate
List.leftpad
List.rightpad
List.reduceOption
List.instEmptyCollection
List.empty_eq
List.isEmpty
List.isEmpty_nil
List.isEmpty_cons
List.elem
List.elem_nil
List.elem_cons
List.contains
List.contains_nil
List.Mem
List.instMembership
List.mem_of_elem_eq_true
List.elem_eq_true_of_mem
List.instDecidableMemOfLawfulBEq
List.mem_append_left
List.mem_append_right
List.decidableBEx
List.decidableBAll
List.take
List.take_nil
List.take_zero
List.take_succ_cons
List.drop
List.drop_nil
List.drop_zero
List.drop_succ_cons
List.drop_eq_nil_of_le
List.extract
List.extract_eq_drop_take
List.takeWhile
List.takeWhile_nil
List.dropWhile
List.dropWhile_nil
List.partition
List.partition.loop
List.dropLast
List.dropLast_nil
List.dropLast_singleton
List.dropLast_single
List.dropLast_cons₂
List.length_dropLast_cons
List.Subset
List.instHasSubset
List.instDecidableRelSubsetOfDecidableEq
List.Sublist
List.«term_<+_»
List.isSublist
List.IsPrefix
List.«term_<+:_»
List.isPrefixOf
List.isPrefixOf_nil_left
List.isPrefixOf_cons_nil
List.isPrefixOf_cons₂
List.isPrefixOf?
List.isSuffixOf
List.isSuffixOf_nil_left
List.isSuffixOf?
List.IsSuffix
List.«term_<:+_»
List.IsInfix
List.«term_<:+:_»
List.splitAt
List.splitAt.go
List.rotateLeft
List.rotateLeft_nil
List.rotateRight
List.rotateRight_nil
List.Pairwise
List.pairwise_cons
List.instDecidablePairwise
List.Nodup
List.nodupDecidable
List.replace
List.replace_nil
List.replace_cons
List.modifyTailIdx
List.modifyTailIdx.go
List.modifyTailIdx_zero
List.modifyTailIdx_succ_nil
List.modifyTailIdx_succ_cons
List.modifyHead
List.modifyHead_nil
List.modifyHead_cons
List.modify
List.insert
List.insertIdx
List.erase
List.erase_nil
List.erase_cons
List.eraseP
List.eraseIdx
List.eraseIdx_nil
List.eraseIdx_cons_zero
List.eraseIdx_cons_succ
List.find?
List.find?_nil
List.find?_cons
List.findSome?
List.findSome?_nil
List.findSome?_cons
List.findRev?
List.findSomeRev?
List.findIdx
List.findIdx.go
List.findIdx_nil
List.idxOf
List.indexOf
List.idxOf_nil
List.indexOf_nil
List.findIdx?
List.findIdx?.go
List.idxOf?
List.indexOf?
List.findFinIdx?
List.findFinIdx?.go
List.finIdxOf?
List.countP
List.countP.go
List.count
List.lookup
List.lookup_nil
List.lookup_cons
List.Perm
List.«term_~_»
List.isPerm
List.any
List.any_nil
List.any_cons
List.all
List.all_nil
List.all_cons
List.or
List.or_nil
List.or_cons
List.and
List.and_nil
List.and_cons
List.zipWith
List.zipWith_nil_left
List.zipWith_nil_right
List.zipWith_cons_cons
List.zip
List.zip_nil_left
List.zip_nil_right
List.zip_cons_cons
List.zipWithAll
List.zipWithAll_nil
List.nil_zipWithAll
List.zipWithAll_cons_cons
List.unzip
List.unzip_nil
List.unzip_cons
List.sum
List.sum_nil
List.sum_cons
List.range
List.range.loop
List.range_zero
List.range'
List.iota
List.iota_zero
List.iota_succ
List.zipIdx
List.zipIdx_nil
List.zipIdx_cons
List.enumFrom
List.enumFrom_nil
List.enumFrom_cons
List.enum
List.enum_nil
List.min?
List.max?
List.intersperse
List.intersperse_nil
List.intersperse_single
List.intersperse_cons₂
List.intercalate
List.eraseDupsBy
List.eraseDupsBy.loop
List.eraseDups
List.eraseRepsBy
List.eraseRepsBy.loop
List.eraseReps
List.span
List.span.loop
List.splitBy
List.splitBy.loop
List.removeAll
List.nil_removeAll
List.length_add_eq_lengthTRAux
List.length_eq_lengthTR
List.mapTR
List.mapTR.loop
List.mapTR_loop_eq
List.map_eq_mapTR
List.filterTR
List.filterTR.loop
List.filterTR_loop_eq
List.filter_eq_filterTR
List.replicateTR
List.replicateTR.loop
List.replicateTR_loop_replicate_eq
List.replicateTR_loop_eq
List.replicate_eq_replicateTR
List.leftpadTR
List.leftpad_eq_leftpadTR
List.unzipTR
List.unzip_eq_unzipTR
List.range'TR
List.range'TR.go
List.range'_eq_range'TR
List.range'_eq_range'TR.go
List.iotaTR
List.iotaTR.go
List.iota_eq_iotaTR
List.intersperseTR
List.intersperse_eq_intersperseTR