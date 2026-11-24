import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2391_2
    (hsize : ∀ (G : SimpleGraph (Fin (26 : ℕ))) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (a b : Fin (26 : ℕ)), G.Adj a b ↔ ∃ (u t : Fin (13 : ℕ)),
        (u = t ∨ u = t + (1 : Fin (13 : ℕ)) ∨ u = t + (3 : Fin (13 : ℕ)) ∨ u = t + (9 : Fin (13 : ℕ))) ∧
        ((a = Fin.castAdd (13 : ℕ) u ∧ b = Fin.natAdd (13 : ℕ) t) ∨
         (b = Fin.castAdd (13 : ℕ) u ∧ a = Fin.natAdd (13 : ℕ) t))) →
      PEqualNP.TopForm.IsLeastAO G C → C.size ≤ 64)
    (hustar : ∀ (G : SimpleGraph (Fin (26 : ℕ))) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (a b : Fin (26 : ℕ)), G.Adj a b ↔ ∃ (u t : Fin (13 : ℕ)),
        (u = t ∨ u = t + (1 : Fin (13 : ℕ)) ∨ u = t + (3 : Fin (13 : ℕ)) ∨ u = t + (9 : Fin (13 : ℕ))) ∧
        ((a = Fin.castAdd (13 : ℕ) u ∧ b = Fin.natAdd (13 : ℕ) t) ∨
         (b = Fin.castAdd (13 : ℕ) u ∧ a = Fin.natAdd (13 : ℕ) t))) →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.Ustar G C = ∅)
    (hcount : ∀ (G : SimpleGraph (Fin (26 : ℕ))) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (a b : Fin (26 : ℕ)), G.Adj a b ↔ ∃ (u t : Fin (13 : ℕ)),
        (u = t ∨ u = t + (1 : Fin (13 : ℕ)) ∨ u = t + (3 : Fin (13 : ℕ)) ∨ u = t + (9 : Fin (13 : ℕ))) ∧
        ((a = Fin.castAdd (13 : ℕ) u ∧ b = Fin.natAdd (13 : ℕ) t) ∨
         (b = Fin.castAdd (13 : ℕ) u ∧ a = Fin.natAdd (13 : ℕ) t))) →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      G.edgeFinset.card + (PEqualNP.TopForm.tops G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
        C.size + (PEqualNP.TopForm.Ustar G C).card + 1)
    (hstruct : ∀ (G : SimpleGraph (Fin (26 : ℕ))) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (a b : Fin (26 : ℕ)), G.Adj a b ↔ ∃ (u t : Fin (13 : ℕ)),
        (u = t ∨ u = t + (1 : Fin (13 : ℕ)) ∨ u = t + (3 : Fin (13 : ℕ)) ∨ u = t + (9 : Fin (13 : ℕ))) ∧
        ((a = Fin.castAdd (13 : ℕ) u ∧ b = Fin.natAdd (13 : ℕ) t) ∨
         (b = Fin.castAdd (13 : ℕ) u ∧ a = Fin.natAdd (13 : ℕ) t))) →
      PEqualNP.TopForm.IsLeastAO G C →
      ∃ C', PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
        PEqualNP.TopForm.TopForm G C' ∧
        (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧
        G.edgeFinset.card = 52 ∧
        (PEqualNP.TopForm.Ustar G C').card + (PEqualNP.TopForm.starEdges G C').card =
          G.edgeFinset.card ∧
        (PEqualNP.TopForm.starEdges G C').card ≤ 4 * (PEqualNP.TopForm.tops G C').card) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj]
      (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)),
        (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧
        (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) →
      PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.junk x1 x3 = ∅ := by
  intro G _ C hG hL
  obtain ⟨C', hL', hsame, htop, hjunk, hedg, hcards, hcover⟩ := hstruct G C hG hL
  have hsizeC : C'.size ≤ 64 := hsize G C' hG hL'
  have hU : PEqualNP.TopForm.Ustar G C' = ∅ := hustar G C' hG hL'
  have hzero : (PEqualNP.TopForm.Ustar G C').card = 0 := Finset.card_eq_zero.mpr hU
  have hcnt : G.edgeFinset.card + (PEqualNP.TopForm.tops G C').card +
      (PEqualNP.TopForm.junk G C').card +
      (PEqualNP.TopForm.orN G C' \ PEqualNP.TopForm.lam G C').card ≤
      C'.size + (PEqualNP.TopForm.Ustar G C').card + 1 :=
    hcount G C' hG hL' htop
  have hstar : (PEqualNP.TopForm.starEdges G C').card = 52 := by omega
  have htops : 13 ≤ (PEqualNP.TopForm.tops G C').card := by omega
  have hcnt' : (PEqualNP.TopForm.tops G C').card + (PEqualNP.TopForm.junk G C').card +
      (PEqualNP.TopForm.orN G C' \ PEqualNP.TopForm.lam G C').card ≤ 13 := by
    omega
  have hzeroJ : (PEqualNP.TopForm.junk G C').card = 0 := by omega
  have hjunk0 : (PEqualNP.TopForm.junk G C).card = 0 := by omega
  exact Finset.card_eq_zero.mp hjunk0
