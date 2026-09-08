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

## TODO

* Extend `IsTree.etreeWidth_le_one` to `IsAcyclic.etreeWidth_le_one` for (possibly disconnected)
  forests, by combining the tree decomposition of each connected component at a fresh hub vertex
  (as `TreeDecomp.bot` does for the empty graph).
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

/-- Every tree has extended treewidth at most `1`. -/
theorem IsTree.etreeWidth_le_one (hG : G.IsTree) : G.etreeWidth ≤ 1 := by
  classical
  obtain ⟨r⟩ := hG.connected.nonempty
  refine (etreeWidth_le_ewidth (hG.treeDecompOfRoot r)).trans ?_
  apply (TreeDecomp.ewidth_le_iff _).mpr
  intro w
  change ({w, hG.parent r w} : Finset V).card - 1 ≤ 1
  have h2 : ({w, hG.parent r w} : Finset V).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  omega

/-- Every tree has treewidth at most `1` (in the finite-vertex-type, `ℕ`-valued sense). -/
theorem IsTree.treeWidth_le_one [Finite V] (hG : G.IsTree) : G.treeWidth ≤ 1 := by
  simpa using hG.etreeWidth_le_one

end SimpleGraph
