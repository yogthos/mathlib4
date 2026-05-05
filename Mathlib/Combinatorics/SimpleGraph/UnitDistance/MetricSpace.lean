/-
Copyright (c) 2026 Dmitri Sotnikov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitri Sotnikov
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring
public import Mathlib.Combinatorics.SimpleGraph.UnitDistance.Basic

/-!
# The unit-distance graph on a metric space

The **unit-distance graph** on a metric space $E$ has vertex set $E$ and an edge between
two distinct points iff they are at distance exactly $1$.

## Main definitions

* `SimpleGraph.unitDistanceGraph E` : the unit-distance graph on the metric space `E`.

## Main results

* `SimpleGraph.UnitDistEmbedding.toHom` : a unit-distance embedding `G.UnitDistEmbedding E`
  yields a graph homomorphism `G →g unitDistanceGraph E`.
* `SimpleGraph.UnitDistEmbedding.colorable_of_colorable` : a proper colouring of
  `unitDistanceGraph E` pulls back to a proper colouring of any graph that has a
  unit-distance embedding into `E`.
* `SimpleGraph.UnitDistEmbedding.chromaticNumber_le_chromaticNumber` :
  `G.chromaticNumber ≤ (unitDistanceGraph E).chromaticNumber` whenever a unit-distance
  embedding exists.

These let one transfer chromatic-number lower bounds from explicit unit-distance graphs (such
as the Moser spindle, `Mathlib.Combinatorics.SimpleGraph.UnitDistance.MoserSpindle`) to the
unit-distance graph on the surrounding metric space, recovering classical Hadwiger–Nelson-style
arguments.

## Tags

unit-distance graph, chromatic number, Hadwiger–Nelson problem
-/

@[expose] public section

namespace SimpleGraph

variable (E : Type*) [MetricSpace E]

/-- The **unit-distance graph** on a metric space: vertex set `E`, with two distinct
points adjacent iff they are at distance exactly $1$. -/
def unitDistanceGraph : SimpleGraph E where
  Adj p q := p ≠ q ∧ dist p q = 1
  symm := by
    intro p q ⟨hne, hd⟩
    refine ⟨hne.symm, ?_⟩
    rw [show (dist q p : ℝ) = dist p q from dist_comm q p]
    exact hd
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

@[simp] lemma unitDistanceGraph_adj {p q : E} :
    (unitDistanceGraph E).Adj p q ↔ p ≠ q ∧ dist p q = 1 := Iff.rfl

variable {E}

namespace UnitDistEmbedding

variable {V : Type*} {G : SimpleGraph V}

/-- A unit-distance embedding induces a graph homomorphism into the metric space's
unit-distance graph. -/
def toHom (φ : G.UnitDistEmbedding E) : G →g unitDistanceGraph E where
  toFun := φ.p
  map_rel' := by
    intro u v huv
    have hd : dist (φ.p u) (φ.p v) = 1 := φ.unit_dist huv
    have hne : φ.p u ≠ φ.p v := fun heq => by
      rw [heq] at hd; simp at hd
    exact ⟨hne, hd⟩

/-- A proper colouring of the unit-distance graph on `E` pulls back along a unit-distance
embedding to a proper colouring of the source graph. -/
theorem colorable_of_colorable (φ : G.UnitDistEmbedding E) {n : ℕ}
    (h : (unitDistanceGraph E).Colorable n) : G.Colorable n :=
  h.of_hom φ.toHom

/-- The chromatic number of `G` is at most that of the unit-distance graph on `E`,
provided a unit-distance embedding exists. -/
theorem chromaticNumber_le_chromaticNumber (φ : G.UnitDistEmbedding E) :
    G.chromaticNumber ≤ (unitDistanceGraph E).chromaticNumber :=
  SimpleGraph.chromaticNumber_mono_of_hom φ.toHom

end UnitDistEmbedding

end SimpleGraph
