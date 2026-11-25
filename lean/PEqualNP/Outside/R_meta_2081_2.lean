import Mathlib
import PEqualNP.Defs

/-- Reduction of L-meta-2081.

The step asks for a circuit of at most 64 AND/OR gates of fan-in two (with distinct
earlier wires) that computes the incidence function of the plane of order 3, is false
at every maximal false input, and reads some incidence twice.  The cut separates the
construction from the three things that have to be checked of it: the shape of the
circuit, the behaviour on incident pairs, the behaviour on the maximal false inputs,
and the double re-read witness. -/
theorem PEqualNP.Outside.R_meta_2081_2
    (hbuild : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) =>
        x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨
          x1 = x2 + (9 : Fin (13 : ℕ));
      have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool)
        (x3 : Fin (13 : ℕ)) =>
        !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) ||
          x2 (x3 + (9 : Fin (13 : ℕ))));
      ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        x3.size ≤ (64 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧
        (∀ x4 ∈ x3.gates, x4.inputs.Nodup))
    (hincident : ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      x3.size ≤ (64 : ℕ) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 →
      (∀ x4 ∈ x3.gates, x4.inputs.Nodup) →
      ∀ (x4 x5 : Fin (13 : ℕ)),
        (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨
          x4 = x5 + (9 : Fin (13 : ℕ))) →
        x3.eval (List.ofFn fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) =>
          Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x4))
            (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true)
    (hfalse : ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      x3.size ≤ (64 : ℕ) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 →
      (∀ x4 ∈ x3.gates, x4.inputs.Nodup) →
      ∀ (x4 : Fin (13 : ℕ) → Bool),
        (∀ (x5 : Fin (13 : ℕ)), x4 x5 = Bool.false →
          ∃ (x7 : Fin (13 : ℕ)),
            ((x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨
              x5 = x7 + (9 : Fin (13 : ℕ))) ∧
              !(x4 x7 || x4 (x7 + (1 : Fin (13 : ℕ))) || x4 (x7 + (3 : Fin (13 : ℕ))) ||
                x4 (x7 + (9 : Fin (13 : ℕ))))) ) →
        x3.eval (List.ofFn fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) =>
          Fin.addCases x4 (fun (x8 : Fin (13 : ℕ)) =>
            !(x4 x8 || x4 (x8 + (1 : Fin (13 : ℕ))) || x4 (x8 + (3 : Fin (13 : ℕ))) ||
              x4 (x8 + (9 : Fin (13 : ℕ))))) x6) = Bool.false)
    (hreread : ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      x3.size ≤ (64 : ℕ) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 →
      (∀ x4 ∈ x3.gates, x4.inputs.Nodup) →
      ∀ (x4 : Bool),
        ∃ (x5 : ℕ → Bool),
          (∀ x6 < (26 : ℕ),
            x5 x6 = Decidable.decide (x6 = if x4 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧
          (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ),
            x3.gates[x6]? = Option.some x7 →
            x7.inputs = [x8, x9] →
            have x12 : List Bool := x3.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) =>
              Decidable.decide (↑x12 = if x4 = Bool.true then (13 : ℕ) else (0 : ℕ)));
            (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and →
              x5 ((26 : ℕ) + x6) = (x12.getD x8 Bool.false && x5 x9 || x5 x8 && x12.getD x9 Bool.false)) ∧
            (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or →
              x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9))) ∧
          x5 x3.output = Bool.false) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) =>
      x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨
        x1 = x2 + (9 : Fin (13 : ℕ));
    have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool)
      (x3 : Fin (13 : ℕ)) =>
      !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) ||
        x2 (x3 + (9 : Fin (13 : ℕ))));
    ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      x3.size ≤ (64 : ℕ) ∧
      PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧
      (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧
      (∀ (x4 x5 : Fin (13 : ℕ)), x1 x4 x5 →
        x3.eval (List.ofFn fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) =>
          Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x4))
            (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧
      (∀ (x4 : Fin (13 : ℕ) → Bool),
        (∀ (x5 : Fin (13 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (13 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) →
        x3.eval (List.ofFn fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) =>
          Fin.addCases x4 (x2 x4) x6) = Bool.false) ∧
      (∀ (x4 : Bool),
        ∃ (x5 : ℕ → Bool),
          (∀ x6 < (26 : ℕ),
            x5 x6 = Decidable.decide (x6 = if x4 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧
          (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ),
            x3.gates[x6]? = Option.some x7 →
            x7.inputs = [x8, x9] →
            have x12 : List Bool := x3.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) =>
              Decidable.decide (↑x12 = if x4 = Bool.true then (13 : ℕ) else (0 : ℕ)));
            (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and →
              x5 ((26 : ℕ) + x6) = (x12.getD x8 Bool.false && x5 x9 || x5 x8 && x12.getD x9 Bool.false)) ∧
            (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or →
              x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9))) ∧
          x5 x3.output = Bool.false) := by
  obtain ⟨x3, hsize, hAO2, hnodup⟩ := hbuild
  have h1 := hincident x3 hsize hAO2 hnodup
  have h2 := hfalse x3 hsize hAO2 hnodup
  have h3 := hreread x3 hsize hAO2 hnodup
  exact ⟨x3, hsize, hAO2, hnodup, h1, h2, h3⟩
