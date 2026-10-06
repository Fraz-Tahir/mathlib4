import Mathlib.Combinatorics.SimpleGraph.TreeDecomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Forests and treewidth

This file relates `SimpleGraph.IsAcyclic` / `SimpleGraph.IsTree` to treewidth.

## Main definitions and results

* `SimpleGraph.IsTree.parent`: given a tree `G` rooted at a vertex `r`, `parent r v` is the
  neighbour of `v` on the (unique) path from `v` to `r`.
* `SimpleGraph.IsTree.parent_eq_of_adj`: every edge of a tree consists of a vertex and its
  parent (with respect to any fixed root).
* `SimpleGraph.IsTree.treeDecompOfRoot`: the tree decomposition of a tree `G` rooted at `r`,
  indexed by `V` itself, with `bag v = {v, parent r v}`.
* `SimpleGraph.IsTree.etreeWidth_le_one`: every tree has (extended) treewidth at most `1`.
* `SimpleGraph.IsAcyclic.etreeWidth_le_one`: every (possibly disconnected) acyclic graph has
  (extended) treewidth at most `1` -- **in progress**, see the `sorry`s in
  `IsAcyclic.isTree_hubTree` and `IsAcyclic.forestDecomp` below.

## TODO

* Finish `IsAcyclic.etreeWidth_le_one`: fill in the `sorry`s in the forest-generalization
  section below (the hub-tree `IsTree` proof, `forestDecomp`'s three `TreeDecomp` obligations,
  and the final width bound).
* The converse: `G.etreeWidth ≤ 1 → G.IsAcyclic`.

## Note

`SimpleGraph.TreeDecomp` indexes bags by a `Type` (universe `0`), so `treeDecompOfRoot`, which
indexes bags by `V` itself, needs `V : Type`.
-/

namespace SimpleGraph

variable {V : Type} {G : SimpleGraph V}

/-- A choice of the (unique, since `G` is a tree) path from `v` to `w`. -/
noncomputable def IsTree.treePath (hG : G.IsTree) (v w : V) : G.Walk v w :=
  (hG.existsUnique_path v w).exists.choose

lemma IsTree.treePath_isPath (hG : G.IsTree) (v w : V) : (hG.treePath v w).IsPath :=
  (hG.existsUnique_path v w).exists.choose_spec

/-- Any two paths between the same pair of vertices in a tree coincide. -/
lemma IsTree.isPath_unique (hG : G.IsTree) {v w : V} {p q : G.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath) : p = q :=
  (hG.existsUnique_path v w).unique hp hq

open Classical in
/-- The parent of `v` in `G`, rooted at `r`: the neighbour of `v` on the (unique) path from `v`
to `r`. The root itself is (arbitrarily) assigned itself as a junk value. -/
noncomputable def IsTree.parent (hG : G.IsTree) (r v : V) : V :=
  if v = r then r else (hG.treePath v r).getVert 1

lemma IsTree.parent_adj (hG : G.IsTree) (r : V) {v : V} (hv : v ≠ r) :
    G.Adj v (hG.parent r v) := by
  have hlen : (hG.treePath v r).length ≠ 0 := by
    intro hzero
    exact hv ((hG.treePath_isPath v r).nil_iff_eq.mp (Walk.length_eq_zero_iff.mp hzero))
  have hadj := (hG.treePath v r).adj_getVert_succ (Nat.pos_of_ne_zero hlen)
  simpa [IsTree.parent, hv] using hadj

/-- If `u` and `v` are adjacent in a tree, one of them is the parent of the other (with respect
to any fixed root `r`). -/
lemma IsTree.parent_eq_of_adj (hG : G.IsTree) (r : V) {u v : V} (huv : G.Adj u v) :
    hG.parent r v = u ∨ hG.parent r u = v := by
  classical
  by_cases h : u ∈ (hG.treePath v r).support
  · left
    have h1 : ((hG.treePath v r).takeUntil u h).IsPath := (hG.treePath_isPath v r).takeUntil h
    have h2 : huv.symm.toWalk.IsPath := huv.symm.isPath_toWalk
    have heq : (hG.treePath v r).takeUntil u h = huv.symm.toWalk := hG.isPath_unique h1 h2
    have hlen : ((hG.treePath v r).takeUntil u h).length = 1 := by
      rw [heq]; exact huv.symm.length_toWalk
    have hgv : (hG.treePath v r).getVert 1 = u := by
      have hh := Walk.getVert_length_takeUntil h
      rwa [hlen] at hh
    have hvr : v ≠ r := by
      intro hv
      subst hv
      have hnil : hG.treePath v v = Walk.nil := hG.isPath_unique (hG.treePath_isPath v v) Walk.IsPath.nil
      rw [hnil] at h
      simp at h
      exact huv.ne h
    simpa [IsTree.parent, hvr] using hgv
  · right
    have hcons : (Walk.cons huv (hG.treePath v r)).IsPath :=
      (Walk.cons_isPath_iff huv (hG.treePath v r)).2 ⟨hG.treePath_isPath v r, h⟩
    have heq : Walk.cons huv (hG.treePath v r) = hG.treePath u r :=
      hG.isPath_unique hcons (hG.treePath_isPath u r)
    have hur : u ≠ r := by
      intro hu
      subst hu
      exact h ((hG.treePath v u).end_mem_support)
    have hgv : (hG.treePath u r).getVert 1 = v := by
      rw [← heq]; simp
    simpa [IsTree.parent, hur] using hgv

open Classical in
/-- The bags of `treeDecompOfRoot` containing a fixed vertex `x` form a preconnected induced
subgraph: every such bag-index is directly adjacent (in `G`) to the one indexed by `x` itself. -/
lemma IsTree.reachable_bag_induce (hG : G.IsTree) (r x : V) :
    (G.induce {w : V | x ∈ ({w, hG.parent r w} : Finset V)}).Preconnected := by
  set S : Set V := {w : V | x ∈ ({w, hG.parent r w} : Finset V)} with hS
  have hxS : x ∈ S := by simp [hS]
  have key : ∀ {w : V} (hw : w ∈ S), (G.induce S).Reachable ⟨w, hw⟩ ⟨x, hxS⟩ := by
    intro w hw
    by_cases hxw : x = w
    · subst hxw; exact Reachable.refl _
    · have hw2 : x = w ∨ x = hG.parent r w := by simpa [hS] using hw
      have hw' : x = hG.parent r w := hw2.resolve_left hxw
      have hwr : w ≠ r := by
        intro h
        subst h
        exact hxw (hw'.trans (by simp [IsTree.parent]))
      have hadj : G.Adj w x := by rw [hw']; exact hG.parent_adj r hwr
      refine ⟨(Walk.cons hadj Walk.nil).induce S (fun y hy => ?_)⟩
      simp at hy
      rcases hy with rfl | rfl
      · exact hw
      · exact hxS
  intro a b
  exact (key a.2).trans (key b.2).symm

open Classical in
/-- Rooting a tree `G` at a vertex `r` gives a tree decomposition of `G`, indexed by `V` itself:
the decomposition tree is `G` itself, and `bag v = {v, parent r v}`. -/
noncomputable def IsTree.treeDecompOfRoot (hG : G.IsTree) (r : V) : G.TreeDecomp V where
  bag v := {v, hG.parent r v}
  tree := G
  isTree := hG
  vertexCover v := by simp
  edgeCover u v huv := by
    rcases hG.parent_eq_of_adj r huv with h | h
    · use v
      rw [h]
      simp only [Finset.mem_insert, Finset.mem_singleton, or_true, true_or, and_self]
    · exact ⟨u, by simp, by simp [h]⟩
  preconnected_induce_T x := hG.reachable_bag_induce r x

open Classical in
/-- The tree decomposition `treeDecompOfRoot` itself (not just `G.etreeWidth`) has width at
most `1` -- extracted from `etreeWidth_le_one`'s proof so the forest generalization below can
reuse this per-component bound directly, rather than only knowing `G.etreeWidth ≤ 1` (an
infimum fact that doesn't hand back a bound on *this specific* decomposition). -/
lemma IsTree.ewidth_treeDecompOfRoot_le_one (hG : G.IsTree) (r : V) :
    (hG.treeDecompOfRoot r).ewidth ≤ 1 := by
  apply (TreeDecomp.ewidth_le_iff _).mpr
  intro w
  change ({w, hG.parent r w} : Finset V).card - 1 ≤ 1
  have h2 : ({w, hG.parent r w} : Finset V).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  omega

/-- Every tree has extended treewidth at most `1`. -/
theorem IsTree.etreeWidth_le_one (hG : G.IsTree) : G.etreeWidth ≤ 1 := by
  obtain ⟨r⟩ := hG.connected.nonempty
  exact (etreeWidth_le_ewidth (hG.treeDecompOfRoot r)).trans (hG.ewidth_treeDecompOfRoot_le_one r)

/-- Every tree has treewidth at most `1` (in the finite-vertex-type, `ℕ`-valued sense). -/
theorem IsTree.treeWidth_le_one [Finite V] (hG : G.IsTree) : G.treeWidth ≤ 1 := by
  simpa using hG.etreeWidth_le_one

/-!
## Forests: generalizing from trees to `IsAcyclic`
-/


/-- A chosen representative vertex of a connected component, used as the root of its own tree
decomposition below. Doesn't need `IsAcyclic` -- just that components are nonempty. -/
noncomputable def ConnectedComponent.chosenRoot (C : G.ConnectedComponent) : ↥C.supp :=
  ⟨C.nonempty_supp.choose, C.nonempty_supp.choose_spec⟩

/-- The tree decomposition of one connected component of an acyclic graph, rooted at its
chosen representative, indexed by that component's own vertex set. -/
noncomputable def IsAcyclic.componentDecomp (hG : G.IsAcyclic) (C : G.ConnectedComponent) :
    C.toSimpleGraph.TreeDecomp C.supp :=
  (hG.isTree_connectedComponent C).treeDecompOfRoot C.chosenRoot

/-- Index type for the forest decomposition: a fresh hub `none`, plus every bag-index of every
component's own tree decomposition, tagged by which component it came from. -/
abbrev ForestIndex (G : SimpleGraph V) := Option (Σ C : G.ConnectedComponent, C.supp)

open Classical in
/-- The decomposition tree gluing every component's own decomposition tree onto a shared fresh
hub vertex `none`, attached via one edge per component to that component's chosen root bag. -/
def IsAcyclic.hubTree (hG : G.IsAcyclic) : SimpleGraph (ForestIndex G) where
  Adj
    | some ⟨C, w⟩, some ⟨C', w'⟩ =>
        if h : C = C' then (hG.componentDecomp C).tree.Adj w (h ▸ w') else False
    | none, some ⟨C, w⟩ => w = C.chosenRoot
    | some ⟨C, w⟩, none => w = C.chosenRoot
    | none, none => False
  symm := by
    constructor
    rintro (_ | ⟨C, w⟩) (_ | ⟨C', w'⟩) hab
    · exact hab.elim
    · exact hab
    · exact hab
    · change if h : C' = C then (hG.componentDecomp C').tree.Adj w' (h ▸ w) else False
      have hab' : if h : C = C' then (hG.componentDecomp C).tree.Adj w (h ▸ w') else False := hab
      by_cases h : C = C'
      · subst h
        rw [dif_pos rfl] at hab'
        rw [dif_pos rfl]
        exact hab'.symm
      · rw [dif_neg h] at hab'
        exact hab'.elim
  loopless := by
    constructor
    rintro (_ | ⟨C, w⟩) hab
    · exact hab
    · have hab' : if h : C = C then (hG.componentDecomp C).tree.Adj w (h ▸ w) else False := hab
      rw [dif_pos rfl] at hab'
      exact (hG.componentDecomp C).tree.irrefl hab'

open Classical in
/-- Each connected component embeds into the hub tree, with adjacency preserved on the nose. -/
def IsAcyclic.componentHom (hG : G.IsAcyclic) (C : G.ConnectedComponent) :
    C.toSimpleGraph →g hG.hubTree where
  toFun w := some ⟨C, w⟩
  map_rel' {a b} hab := by
    change if h : C = C then (hG.componentDecomp C).tree.Adj a (h ▸ b) else False
    rw [dif_pos rfl]
    exact hab

/-- The component homomorphism is injective. 
if you map a path along an injective graph homomorphism, the result is still a path.
Injectivity is the whole point here, 
if the embedding could send two different vertices of C.toSimpleGraph to the same vertex of hG.hubTree,
a path with no repeats could turn into a walk with repeats after mapping-/
lemma IsAcyclic.componentHom_injective (hG : G.IsAcyclic) (C : G.ConnectedComponent) :
    Function.Injective (hG.componentHom C) := by
  intro a b hab
  simpa [IsAcyclic.componentHom] using hab

/-- The hub is adjacent to exactly the chosen root of every component. -/
lemma IsAcyclic.hubTree_adj_none_chosenRoot (hG : G.IsAcyclic) (C : G.ConnectedComponent) :
    hG.hubTree.Adj none (some ⟨C, C.chosenRoot⟩) := rfl

/-- The only neighbours of a component vertex `some ⟨C, x⟩` in `hubTree` are `none`
(reached exactly when `x` is the chosen root) or another vertex of the same component. -/
lemma IsAcyclic.hubTree_adj_some_elim (hG : G.IsAcyclic) {C : G.ConnectedComponent} {x : ↥C.supp}
    {v : ForestIndex G} (hadj : hG.hubTree.Adj (some ⟨C, x⟩) v) :
    v = none ∨ ∃ y : ↥C.supp, v = some ⟨C, y⟩ := by
  cases v with
  | none => exact Or.inl rfl
  | some p =>
    obtain ⟨C', y⟩ := p
    by_cases hCC : C = C'
    · subst hCC; exact Or.inr ⟨y, rfl⟩
    · exfalso
      classical
      change (if h : C = C' then (hG.componentDecomp C).tree.Adj x (h ▸ y) else False) at hadj
      rw [dif_neg hCC] at hadj
      exact hadj

/-- Any path from a component's vertex to the hub stays entirely inside that component
until it reaches `none`. -/
lemma IsAcyclic.support_subset_component_of_walk_to_none (hG : G.IsAcyclic)
    (C : G.ConnectedComponent) (x : ↥C.supp) (p : hG.hubTree.Walk (some ⟨C, x⟩) none)
    (hp : p.IsPath) :
    ∀ u ∈ p.support, u = none ∨ ∃ w : ↥C.supp, u = some ⟨C, w⟩ := by
  suffices H : ∀ {src tgt : ForestIndex G} (p : hG.hubTree.Walk src tgt), tgt = none →
      p.IsPath → (src = none ∨ ∃ x : ↥C.supp, src = some ⟨C, x⟩) →
      ∀ u ∈ p.support, u = none ∨ ∃ w : ↥C.supp, u = some ⟨C, w⟩ by
    exact H p rfl hp (Or.inr ⟨x, rfl⟩)
  intro src tgt p
  induction p with
  | nil =>
      intro htgt _ _ u hu
      simp only [Walk.support_nil, List.mem_singleton] at hu
      exact Or.inl (hu.trans htgt)
  | cons hadj p' ih =>
      intro htgt hcons hsrc u hu
      rw [Walk.cons_isPath_iff] at hcons
      rw [Walk.support_cons, List.mem_cons] at hu
      rcases hu with rfl | hu'
      · exact hsrc
      · refine ih htgt hcons.1 ?_ u hu'
        rcases hsrc with heq | ⟨x', heq⟩
        · rw [heq] at hadj hcons
          exact absurd (htgt ▸ Walk.end_mem_support p') hcons.2
        · rw [heq] at hadj
          exact hG.hubTree_adj_some_elim hadj

lemma IsAcyclic.exists_isPath_hubTree (hG : G.IsAcyclic) :
    ∀ v w : ForestIndex G, ∃ p : hG.hubTree.Walk v w, p.IsPath
  | none, none => ⟨Walk.nil, Walk.IsPath.nil⟩
  | none, some ⟨C, x⟩ =>
    ⟨Walk.cons (hG.hubTree_adj_none_chosenRoot C)
      (show hG.hubTree.Walk (some ⟨C, C.chosenRoot⟩) (some ⟨C, x⟩) from
        ((hG.isTree_connectedComponent C).treePath C.chosenRoot x).map (hG.componentHom C)),
     by
       rw [Walk.cons_isPath_iff]
       refine ⟨((hG.isTree_connectedComponent C).treePath_isPath _ _).map
         (hG.componentHom_injective C), ?_⟩
       simp [Walk.support_map, IsAcyclic.componentHom]⟩
  | some ⟨C, x⟩, none =>
      let ⟨p, hp⟩ := hG.exists_isPath_hubTree none (some ⟨C, x⟩); ⟨p.reverse, hp.reverse⟩
  | some ⟨C, x⟩, some ⟨C', y⟩ => by
    by_cases h : C = C'
    · subst h
      exact ⟨((hG.isTree_connectedComponent C).treePath x y).map (hG.componentHom C),
        ((hG.isTree_connectedComponent C).treePath_isPath x y).map (hG.componentHom_injective C)⟩
    · obtain ⟨p1, hp1⟩ := hG.exists_isPath_hubTree (some ⟨C, x⟩) none
      obtain ⟨p2, hp2⟩ := hG.exists_isPath_hubTree none (some ⟨C', y⟩)
      -- `none` is the head of `p2.support`; since `p2` is a path it can't recur in the tail.
      have hp2none : none ∉ p2.support.tail := by
        obtain ⟨z, hadj, p2', rfl⟩ :=
          p2.exists_eq_cons_of_ne (by simp : (none : ForestIndex G) ≠ some ⟨C', y⟩)
        simpa using (List.nodup_cons.mp hp2.support_nodup).1
      refine ⟨p1.append p2, Walk.IsPath.mk' ?_⟩
      rw [Walk.support_append]
      refine List.Nodup.append hp1.support_nodup hp2.support_nodup.tail ?_
      intro u hu1 hu2
      rcases hG.support_subset_component_of_walk_to_none C x p1 hp1 u hu1 with rfl | ⟨w, rfl⟩
      · exact hp2none hu2
      · rcases hG.support_subset_component_of_walk_to_none C' y p2.reverse hp2.reverse
          (some ⟨C, w⟩) (by simpa using List.mem_of_mem_tail hu2) with h' | ⟨w', hw'⟩
        · exact Option.some_ne_none _ h'
        · exact h (Sigma.mk.inj (Option.some.inj hw')).1
                   
/-- **TODO -- the key new lemma.** The hub-glued tree is actually a tree: connectivity routes
within one component's own tree, or through the hub; acyclicity holds because a cycle would
have to stay inside one already-acyclic component's sub-tree, or use the hub at least twice --
but each component touches the hub via exactly one designated edge, so no cycle can close
through the hub either. This is the piece to design together, not to guess at blindly. -/
lemma IsAcyclic.isTree_hubTree (hG : G.IsAcyclic) : hG.hubTree.IsTree := by
  sorry

/-- The tree decomposition of a (possibly disconnected) acyclic graph `G`: glue each connected
component's own tree decomposition onto a shared hub. -/
noncomputable def IsAcyclic.forestDecomp (hG : G.IsAcyclic) : G.TreeDecomp (ForestIndex G) where
  bag
    | none => ∅
    | some ⟨C, w⟩ => ((hG.componentDecomp C).bag w).map ⟨Subtype.val, Subtype.val_injective⟩
  tree := hG.hubTree
  isTree := hG.isTree_hubTree
  vertexCover v := by
    sorry -- TODO: v lies in its own component `C := G.connectedComponentMk v`; reduce to
          -- `(hG.componentDecomp C).vertexCover`.
  edgeCover u v huv := by
    sorry -- TODO: `huv : G.Adj u v` implies `u`, `v` are in the same component (`Adj` implies
          -- `Reachable`); reduce to that component's own `edgeCover`.
  preconnected_induce_T x := by
    sorry -- TODO: every bag containing `x` lives in `x`'s own component's slice (bag `none`
          -- is `∅`, so it never contains `x`); reduces to that component's own
          -- `preconnected_induce_T`, transported through the `some ⟨C, ·⟩` embedding.

/-- Every (possibly disconnected) acyclic graph has extended treewidth at most `1`. -/
theorem IsAcyclic.etreeWidth_le_one (hG : G.IsAcyclic) : G.etreeWidth ≤ 1 := by
  refine (etreeWidth_le_ewidth hG.forestDecomp).trans ?_
  sorry -- TODO: `none`'s bag has card `0`; `some ⟨C, w⟩`'s bag has the same card as
        -- `(hG.componentDecomp C).bag w` (image under an injective map), bounded by
        -- `(hG.isTree_toSimpleGraph C).ewidth_treeDecompOfRoot_le_one C.chosenRoot`.

end SimpleGraph
