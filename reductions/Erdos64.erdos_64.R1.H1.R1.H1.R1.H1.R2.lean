import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Set.Card.Arithmetic

/-
Copyright (c) 2026 Nealanio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Decompose the nonbipartite bridgeless cubic case through a perfect matching

H1 is Petersen's perfect-matching theorem for connected bridgeless cubic graphs. H2 is the
normal form obtained after deleting that matching: a spanning degree-two factor edge-disjoint
from the matching and covering every edge with it.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H1_R2

open SimpleGraph

/-- Connected bridgeless cubic graphs have a perfect matching. -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.Connected → (∀ x, G.degree x = 3) →
    (∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a, b)) →
    ∃ M : G.Subgraph, M.IsPerfectMatching

/-- A connected nonbipartite graph decomposed into a perfect matching and an edge-disjoint
spanning degree-two factor has a power-of-two cycle. -/
def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.Connected → ¬ G.IsBipartite →
    ∀ M F : G.Subgraph,
      [∀ v, Fintype (F.neighborSet v)] →
      M.IsPerfectMatching → F.IsSpanning →
      (∀ v, F.degree v = 2) →
      (∀ v w, M.Adj v w → ¬ F.Adj v w) →
      (∀ v w, G.Adj v w → M.Adj v w ∨ F.Adj v w) →
      ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

theorem perfectMatching_complement_degree_two
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (deg3 : ∀ x, G.degree x = 3)
    (M : G.Subgraph) (hM : M.IsPerfectMatching) (v : V)
    [Fintype (((⊤ : G.Subgraph).deleteEdges M.edgeSet).neighborSet v)] :
    ((⊤ : G.Subgraph).deleteEdges M.edgeSet).degree v = 2 := by
  classical
  obtain ⟨m, hm, huniq⟩ := (Subgraph.isPerfectMatching_iff.mp hM) v
  let F : G.Subgraph := (⊤ : G.Subgraph).deleteEdges M.edgeSet
  have hset : F.neighborSet v = G.neighborSet v \ {m} := by
    ext w
    constructor
    · intro hw
      change F.Adj v w at hw
      have htop : (⊤ : G.Subgraph).Adj v w := hw.1
      constructor
      · exact Subgraph.top_adj.mp htop
      · intro hwm
        subst hwm
        exact hw.2 (by simpa [Subgraph.mem_edgeSet] using hm)
    · intro hw
      change F.Adj v w
      constructor
      · exact Subgraph.top_adj.mpr hw.1
      · intro hed
        have hmadj : M.Adj v w := by simpa [Subgraph.mem_edgeSet] using hed
        exact hw.2 (huniq w hmadj)
  change Fintype.card (F.neighborSet v) = 2
  rw [Set.fintypeCard_eq_ncard, hset]
  have hmG : m ∈ G.neighborSet v := M.adj_sub hm
  rw [Set.ncard_sdiff_singleton_of_mem hmG]
  have hfcard : Fintype.card (G.neighborSet v) = G.degree v := card_neighborSet_eq_degree G v
  rw [Set.fintypeCard_eq_ncard, deg3 v] at hfcard
  omega

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.H1 := by
  intro petersen normalform V G finite dec hconn hcubic hbridge hnonbip
  classical
  obtain ⟨M, hM⟩ := petersen V G hconn hcubic hbridge
  let F : G.Subgraph := (⊤ : G.Subgraph).deleteEdges M.edgeSet
  have hspan : F.IsSpanning := by
    intro x
    simp [F]
  have hdeg : ∀ v, F.degree v = 2 := by
    intro v
    exact perfectMatching_complement_degree_two hcubic M hM v
  have hdisjoint : ∀ v w, M.Adj v w → ¬ F.Adj v w := by
    intro v w hm hf
    have hmem : s(v, w) ∈ M.edgeSet := (Subgraph.mem_edgeSet).mpr hm
    exact hf.2 hmem
  have hcover : ∀ v w, G.Adj v w → M.Adj v w ∨ F.Adj v w := by
    intro v w hg
    by_cases hm : M.Adj v w
    · exact Or.inl hm
    · right
      change (⊤ : G.Subgraph).Adj v w ∧ s(v, w) ∉ M.edgeSet
      constructor
      · exact Subgraph.top_adj.mpr hg
      · intro hmem
        exact hm ((Subgraph.mem_edgeSet).mp hmem)
  exact normalform V G hconn hnonbip M F hM hspan hdeg hdisjoint hcover

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H1_R2
