module

-- Auditor-2: kernel evaluation of Lean definitions against the Python values (cfgW, n = 1).
-- To run: copy to Zeta2Lean/Scratch/ and  bash scripts/check.sh Zeta2Lean/Scratch/<file>  (about 50 s, exit 0).
-- Last run 2026-09-25: exit=0, every example accepted.
public import Zeta2Lean.Window.Defs

@[expose] public section

/-! Auditor-2 scratch: kernel evaluation of the Lean definitions against the auditor's Python values
(cfgW, n = 1).  Not part of the build; delete after use. -/

open ZetaWindow

-- `/` on `ℤ` rounds toward -∞ for a positive divisor (floor division), as JTNB (8.9) needs
example : ((-7 : ℤ) / 2) = -4 := by decide
example : ((-1 : ℤ) / 13) = -1 := by decide
example : ((-13 : ℤ) / 13) = -1 := by decide
example : ((-14 : ℤ) / 13) = -2 := by decide

-- omega_{k,p} literally (Python: omega_{51,13} = 14, omega_{0,59} = 15, omega_{100,59} = 17)
example : omegaKP cfgW 1 13 51 = 14 := by decide +kernel
example : omegaKP cfgW 1 59 0 = 15 := by decide +kernel
example : omegaKP cfgW 1 59 100 = 17 := by decide +kernel
-- omega_p = min over a full residue system (Python: 12 for p = 13)
example : omegaP cfgW 1 13 = 12 := by decide +kernel

-- m_j and the lcm product
example : (List.range 18).map (fun j => mj cfgW 1 (j + 1)) =
    [63, 63, 62, 61, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60] := by decide +kernel

set_option maxRecDepth 100000 in
example : PhiN cfgW 1 = 8800167420338850402021129626336419514939588676511312936710053800161757308220632250812661001589022277825221122399850694061013831207907535573342026642456471345351606214441079 := by
  decide +kernel

set_option maxRecDepth 100000 in
example : Dprod cfgW 1 = 960426100815482812775590508164766349502048317704843443319986948012696684128091501036920154499316806639718685689981709280916430646681340408181120246572085855834947359687559303038188796097165311057031346622836060426474336305865449483921233204604614412132103770520878088223203616977228186065734846676132400537247085719248112431038015119923739183947986589713707106831688586371021644925944421006488426140447141152552944800737998510729757928853021409924823293140838708728138444466278112166901853169717320896865571201268213350400000000000000000000000000000000000000000000 := by
  decide +kernel

-- the constants
example : (C2hi : ℚ) < C0lo := by norm_num [C2hi, C0lo]
example : mu cfgW (cfgW.q - cfgW.r) = 60 := by decide
