import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1207

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The circuit of the sketch for the graph n8-058 (edges 01 02 13 24 35 45 67): wire `8` is
`x1 OR x2`, wire `9` is `x0 AND wire 8`, wire `10` is `x1 OR x5`, wire `11` is `x3 AND wire 10`,
wire `12` is `x2 OR x5`, wire `13` is `x4 AND wire 12`, wire `14` is `x6 AND x7`, wire `15` is
`wire 9 OR wire 11`, wire `16` is `wire 15 OR wire 13` and wire `17` is `wire 16 OR wire 14`,
which is the output. -/
def C0 : Circuit :=
  ⟨[ ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [1, 5]⟩,
      ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [4, 12]⟩,
      ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 13]⟩,
      ⟨GateOp.or, [16, 14]⟩ ], 17⟩

theorem ok0 : Monotone2 C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ofFn8 (x : Fin 8 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

theorem ev0 : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Bool),
    C0.eval [b0, b1, b2, b3, b4, b5, b6, b7] =
      ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b5) || (b4 && b5) ||
        (b6 && b7)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1207

theorem PEqualNP.Outside.L_meta_1207 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 6 && x 7)) x :=
  ⟨PEqualNP.Outside.L_meta_1207.C0, PEqualNP.Outside.L_meta_1207.ok0, by decide,
    fun x => by
      rw [PEqualNP.Outside.L_meta_1207.ofFn8]
      exact PEqualNP.Outside.L_meta_1207.ev0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)⟩
