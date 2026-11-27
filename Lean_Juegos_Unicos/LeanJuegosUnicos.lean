/-!
# Lean Juegos Únicos — Capa Autónoma de Auditoría Formal (v0.3)

Autor: José Luis López Rangel
Archivo: LeanJuegosUnicos.lean
Entorno objetivo: Lean 4 puro (4.34.1 / 4.35.0 / 4.36.0), cero imports, cero Mathlib,
cero `sorry`, cero axiomas propios, cero `native_decide`.

## Cobertura de auditoría frente a *Unique Games* v0.3
1. **Núcleo racional exacto (`Q`)**: aritmética y orden exactos, desigualdades constructivas
   tipo Bernoulli en ambos sentidos (`(1 - p)^k (1 + k p) ≤ 1` y `(1 + x)^k (1 - k x) ≤ 1`),
   cota lineal `(1 + x)^k - 1 ≤ 2 k x` bajo `2 k x ≤ 1` y testigo finito `pow_lt_of_witness`.
2. **Fibras buenas, divergencia χ² y genealogía de `decodingMass` (Secciones 5–7 y 16)**:
   positividad de `g₀ = 10 η² 2^(-l r_s)`, derivación exacta por bloque singleton
   `χ²(P ‖ U) = (n - 1) / 3`, divergencia acumulada `chiSqTotal`, genealogía exacta
   `visibleMass * conditionalMass = decodingMass` y colapso a cero cuando `g₀ = 0`.
3. **Coordenadas limpias y régimen acoplado `β = k^(-2/3)` (Secciones 6, 8 y 9)**:
   monotonicidad en `rank A ≤ r_s`, positividad de `D(k)` en todo `k` finito, y
   **teorema acoplado simultáneo** (`exists_coupled_two_thirds_regime`): con `k = m³`
   y `β = 1 / m²` demuestra a la vez `chiSqTotal n k β < τ` y `D(k) < decodingMass`.
4. **Ventana de escalamiento y balances de `β = k^(-a)` (Sección 9)**:
   equivalencia exacta `1/2 < a < 1`, unicidad del balance simétrico en `a = 2/3`
   (tasa común `k^(-1/3)`) y balance en variación total `TV_k` en `a = 3/4`
   (tasa común `k^(-1/4)`).
5. **Probabilidad finita y costura de carga (Sección 10)**:
   `FinDist`, `actualAgreement`, `fullSeedAgreement` y `noHiddenConditioning_of_same_law`.
6. **Teorema de costura global `WitnessMassFlow` y `ProbWitnessMassFlow` (Secciones 11 y 14)**:
   cierre exacto `L ≤ A_act = A_full ≤ D < L → False` con observable `Agr : Ω → [0, 1]`.
7. **Controles negativos constructivos sobre `Ω = {0,1}²` (Sección 12)**:
   Proposiciones 12.1 (certificando explícitamente `A_act ≠ A_full`), 12.2 (acuerdo positivo sin
   separación estricta) y 12.3 (con `g₀ = 0`, ningún `k` finito logra `D(k) < L`).
8. **Torre no circular de parámetros `ParameterTower` (Secciones 13 y 14)**:
   tipos dependientes por etapas, presupuesto `k * ξ + p_* / 2 ≤ ε₀ / t`,
   construcción canónica general (`OuterStage.canonical`, `ParameterTower.canonical`) para
   cualquier objetivo `(ε, δ) > 0`, y testigo explícito `ParameterTower.exampleWitness`.
9. **Interfaz auditable de entradas importadas `SoundnessAuditBundle` (Límite 14.1)**
   y auditoría final de axiomas del kernel mediante `#print axioms`.
-/

namespace JuegosUnicos

/-! ============================================================================
    SECCIÓN 1. LEMAS AUXILIARES AUTOCONTENIDOS EN `Int` Y POTENCIAS DE 2
    ============================================================================ -/

private theorem nat_mul_pos_aux {m n : Nat} (hm : 0 < m) (hn : 0 < n) : 0 < m * n := by
  cases n with
  | zero => omega
  | succ n' =>
    rw [Nat.mul_succ]
    omega

private theorem int_ofNat_add (m n : Nat) : Int.ofNat (m + n) = Int.ofNat m + Int.ofNat n := rfl

private theorem int_ofNat_mul (m n : Nat) : Int.ofNat (m * n) = Int.ofNat m * Int.ofNat n := rfl

private theorem int_ofNat_le {m n : Nat} (h : m ≤ n) : Int.ofNat m ≤ Int.ofNat n := by
  have hsub : m + (n - m) = n := by omega
  have hadd : Int.ofNat m + Int.ofNat (n - m) = Int.ofNat n := by
    rw [← int_ofNat_add, hsub]
  have hnn : 0 ≤ Int.ofNat (n - m) := Int.natCast_nonneg (n - m)
  omega

private theorem int_ofNat_lt {m n : Nat} (h : m < n) : Int.ofNat m < Int.ofNat n := by
  have hsub : m + (n - m) = n := by omega
  have hadd : Int.ofNat m + Int.ofNat (n - m) = Int.ofNat n := by
    rw [← int_ofNat_add, hsub]
  have hpos : 0 < Int.ofNat (n - m) := Int.natCast_pos.mpr (by omega)
  omega

private theorem int_mul_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      change 0 ≤ Int.ofNat (m * n)
      exact Int.natCast_nonneg (m * n)
    | negSucc n => omega
  | negSucc m => omega

private theorem int_mul_pos {a b : Int} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      have hm : 0 < m := Int.natCast_pos.mp ha
      have hn : 0 < n := Int.natCast_pos.mp hb
      have hmn : 0 < m * n := nat_mul_pos_aux hm hn
      change 0 < Int.ofNat (m * n)
      exact Int.natCast_pos.mpr hmn
    | negSucc n => omega
  | negSucc m => omega

private theorem int_mul_sub (a b c : Int) : a * (b - c) = a * b - a * c := by
  rw [Int.mul_comm a (b - c), Int.sub_mul, Int.mul_comm b a, Int.mul_comm c a]

private theorem int_mul_right_comm (a b c : Int) : a * b * c = a * c * b := by
  rw [Int.mul_assoc, Int.mul_comm b c, ← Int.mul_assoc]

private theorem int_mul4 (w x y z : Int) : (w * x) * (y * z) = (w * y) * (x * z) := by
  rw [← Int.mul_assoc, int_mul_right_comm w x y, Int.mul_assoc]

private theorem int_mul_le_mul_right {a b c : Int} (hab : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  have h1 : 0 ≤ b - a := by omega
  have h2 : 0 ≤ (b - a) * c := int_mul_nonneg h1 hc
  rw [Int.sub_mul] at h2
  omega

private theorem int_mul_le_mul_left {a b c : Int} (hab : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  rw [Int.mul_comm c a, Int.mul_comm c b]
  exact int_mul_le_mul_right hab hc

private theorem int_mul_lt_mul_right {a b c : Int} (hab : a < b) (hc : 0 < c) : a * c < b * c := by
  have h1 : 0 < b - a := by omega
  have h2 : 0 < (b - a) * c := int_mul_pos h1 hc
  rw [Int.sub_mul] at h2
  omega

private theorem int_le_of_mul_right {a b c : Int} (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b :=
  if hba : b < a then
    False.elim (by have := int_mul_lt_mul_right hba hc; omega)
  else
    by omega

private theorem int_lt_of_mul_right {a b c : Int} (h : a * c < b * c) (hc : 0 < c) : a < b :=
  if hba : b ≤ a then
    False.elim (by have := int_mul_le_mul_right (c := c) hba (by omega : 0 ≤ c); omega)
  else
    by omega

private theorem int_eq_of_mul_right {a b c : Int} (h : a * c = b * c) (hc : 0 < c) : a = b := by
  have h1 : a ≤ b := int_le_of_mul_right (by omega) hc
  have h2 : b ≤ a := int_le_of_mul_right (by omega) hc
  omega

private theorem int_ofNat_toNat {a : Int} (ha : 0 ≤ a) : Int.ofNat a.toNat = a := by
  cases a with
  | ofNat n => rfl
  | negSucc n => omega

/-- Potencias exactas `2^n` en `Int`, sin dependencias externas. -/
def pow2Int : Nat → Int
  | 0 => 1
  | n + 1 => 2 * pow2Int n

theorem pow2Int_pos : ∀ n : Nat, 0 < pow2Int n
  | 0 => by decide
  | n + 1 => by
      have ih := pow2Int_pos n
      dsimp [pow2Int]
      omega

theorem pow2Int_ge_one (n : Nat) : 1 ≤ pow2Int n := by
  have h := pow2Int_pos n
  omega

theorem pow2Int_add : ∀ a b : Nat, pow2Int (a + b) = pow2Int a * pow2Int b
  | 0, b => by
      dsimp [pow2Int]
      rw [Nat.zero_add, Int.one_mul]
  | a + 1, b => by
      rw [Nat.succ_add]
      dsimp [pow2Int]
      rw [pow2Int_add a b, ← Int.mul_assoc]

theorem pow2Int_mono {a b : Nat} (h : a ≤ b) : pow2Int a ≤ pow2Int b := by
  have hba : a + (b - a) = b := by omega
  rw [← hba, pow2Int_add]
  have h1 : 1 ≤ pow2Int (b - a) := pow2Int_ge_one (b - a)
  have ha : 0 ≤ pow2Int a := by
    have := pow2Int_pos a
    omega
  have hmul := int_mul_le_mul_left h1 ha
  rw [Int.mul_one] at hmul
  exact hmul

/-! ============================================================================
    SECCIÓN 2. NÚCLEO RACIONAL EXACTO `Q` Y COTAS DE BERNOULLI CONSTRUCTIVAS
    ============================================================================ -/

/-- Racionales exactos representados como `(num, den)` con `den > 0`. -/
structure Q where
  num : Int
  den : Int
  den_pos : 0 < den

namespace Q

def zero : Q := ⟨0, 1, by decide⟩
def one : Q := ⟨1, 1, by decide⟩
def half : Q := ⟨1, 2, by decide⟩
def quarter : Q := ⟨1, 4, by decide⟩
def eighth : Q := ⟨1, 8, by decide⟩
def threeEighths : Q := ⟨3, 8, by decide⟩
def twoThirds : Q := ⟨2, 3, by decide⟩
def threeFourths : Q := ⟨3, 4, by decide⟩
def negOneThird : Q := ⟨-1, 3, by decide⟩
def negOneQuarter : Q := ⟨-1, 4, by decide⟩

def ofInt (n : Int) : Q := ⟨n, 1, by decide⟩
def ofNat (n : Nat) : Q := ⟨Int.ofNat n, 1, by decide⟩
def mkPos (n d : Int) (hd : 0 < d) : Q := ⟨n, d, hd⟩

def Eqv (x y : Q) : Prop := x.num * y.den = y.num * x.den
def LE (x y : Q) : Prop := x.num * y.den ≤ y.num * x.den
def LT (x y : Q) : Prop := x.num * y.den < y.num * x.den

instance instDecEqv (x y : Q) : Decidable (Eqv x y) :=
  inferInstanceAs (Decidable (x.num * y.den = y.num * x.den))

instance instDecLE (x y : Q) : Decidable (LE x y) :=
  inferInstanceAs (Decidable (x.num * y.den ≤ y.num * x.den))

instance instDecLT (x y : Q) : Decidable (LT x y) :=
  inferInstanceAs (Decidable (x.num * y.den < y.num * x.den))

def add (x y : Q) : Q :=
  ⟨x.num * y.den + y.num * x.den, x.den * y.den, int_mul_pos x.den_pos y.den_pos⟩

def neg (x : Q) : Q :=
  ⟨-x.num, x.den, x.den_pos⟩

def sub (x y : Q) : Q :=
  ⟨x.num * y.den - y.num * x.den, x.den * y.den, int_mul_pos x.den_pos y.den_pos⟩

def mul (x y : Q) : Q :=
  ⟨x.num * y.num, x.den * y.den, int_mul_pos x.den_pos y.den_pos⟩

def divPos (x y : Q) (hy : 0 < y.num) : Q :=
  ⟨x.num * y.den, x.den * y.num, int_mul_pos x.den_pos hy⟩

def pow (x : Q) : Nat → Q
  | 0 => one
  | k + 1 => mul (pow x k) x

theorem eqv_refl (x : Q) : Eqv x x := rfl

theorem eqv_symm {x y : Q} (h : Eqv x y) : Eqv y x := h.symm

theorem eqv_trans {x y z : Q} (hxy : Eqv x y) (hyz : Eqv y z) : Eqv x z := by
  dsimp [Eqv] at hxy hyz ⊢
  have h1 : (x.num * y.den) * z.den = (y.num * x.den) * z.den := by rw [hxy]
  have h2 : (y.num * z.den) * x.den = (z.num * y.den) * x.den := by rw [hyz]
  rw [int_mul_right_comm x.num y.den z.den, int_mul_right_comm y.num x.den z.den] at h1
  rw [int_mul_right_comm z.num y.den x.den] at h2
  exact int_eq_of_mul_right (h1.trans h2) y.den_pos

theorem le_refl (x : Q) : LE x x := by
  dsimp [LE]; omega

theorem le_of_eqv {x y : Q} (h : Eqv x y) : LE x y := by
  dsimp [Eqv] at h
  dsimp [LE]
  omega

theorem le_of_lt {x y : Q} (h : LT x y) : LE x y := by
  dsimp [LT] at h
  dsimp [LE]
  omega

theorem le_trans {x y z : Q} (hxy : LE x y) (hyz : LE y z) : LE x z := by
  dsimp [LE] at hxy hyz ⊢
  have h1 := int_mul_le_mul_right (c := z.den) hxy (by have := z.den_pos; omega)
  have h2 := int_mul_le_mul_right (c := x.den) hyz (by have := x.den_pos; omega)
  rw [int_mul_right_comm x.num y.den z.den, int_mul_right_comm y.num x.den z.den] at h1
  rw [int_mul_right_comm z.num y.den x.den] at h2
  exact int_le_of_mul_right (by omega) y.den_pos

theorem lt_of_le_of_lt {x y z : Q} (hxy : LE x y) (hyz : LT y z) : LT x z := by
  dsimp [LE, LT] at hxy hyz ⊢
  have h1 := int_mul_le_mul_right (c := z.den) hxy (by have := z.den_pos; omega)
  have h2 := int_mul_lt_mul_right hyz x.den_pos
  rw [int_mul_right_comm x.num y.den z.den, int_mul_right_comm y.num x.den z.den] at h1
  rw [int_mul_right_comm z.num y.den x.den] at h2
  exact int_lt_of_mul_right (by omega) y.den_pos

theorem lt_of_lt_of_le {x y z : Q} (hxy : LT x y) (hyz : LE y z) : LT x z := by
  dsimp [LE, LT] at hxy hyz ⊢
  have h1 := int_mul_lt_mul_right hxy z.den_pos
  have h2 := int_mul_le_mul_right (c := x.den) hyz (by have := x.den_pos; omega)
  rw [int_mul_right_comm x.num y.den z.den, int_mul_right_comm y.num x.den z.den] at h1
  rw [int_mul_right_comm z.num y.den x.den] at h2
  exact int_lt_of_mul_right (by omega) y.den_pos

theorem not_lt_of_le {x y : Q} (h : LE x y) : ¬ LT y x := by
  intro hlt
  dsimp [LE] at h
  dsimp [LT] at hlt
  omega

theorem nonneg_iff {x : Q} : LE zero x ↔ 0 ≤ x.num := by
  simp only [LE, zero, Int.zero_mul, Int.mul_one]

theorem pos_iff {x : Q} : LT zero x ↔ 0 < x.num := by
  simp only [LT, zero, Int.zero_mul, Int.mul_one]

theorem add_comm_eqv (x y : Q) : Eqv (add x y) (add y x) := by
  dsimp [Eqv, add]
  rw [Int.add_comm (x.num * y.den) (y.num * x.den), Int.mul_comm x.den y.den]

theorem mul_comm_eqv (x y : Q) : Eqv (mul x y) (mul y x) := by
  dsimp [Eqv, mul]
  rw [Int.mul_comm x.num y.num, Int.mul_comm x.den y.den]

theorem mul_assoc_eqv (x y z : Q) : Eqv (mul (mul x y) z) (mul x (mul y z)) := by
  dsimp [Eqv, mul]
  rw [Int.mul_assoc x.num y.num z.num, Int.mul_assoc x.den y.den z.den]

theorem add_le_add_right {a b c : Q} (hab : LE a b) : LE (add a c) (add b c) := by
  dsimp [LE, add] at hab ⊢
  rw [Int.add_mul, Int.add_mul]
  rw [int_mul4 a.num c.den b.den c.den]
  rw [int_mul4 b.num c.den a.den c.den]
  rw [int_mul4 c.num a.den b.den c.den]
  have hc2 : 0 ≤ c.den * c.den := by
    have := int_mul_pos c.den_pos c.den_pos
    omega
  have h1 := int_mul_le_mul_right hab hc2
  omega

theorem add_le_add {a b c d : Q} (hab : LE a b) (hcd : LE c d) : LE (add a c) (add b d) := by
  have h1 : LE (add a c) (add b c) := add_le_add_right hab
  have h2 : LE (add c b) (add d b) := add_le_add_right hcd
  have h3 : LE (add b c) (add b d) :=
    le_trans (le_of_eqv (add_comm_eqv b c)) (le_trans h2 (le_of_eqv (add_comm_eqv d b)))
  exact le_trans h1 h3

theorem add_eqv_add_right {a b c : Q} (hab : Eqv a b) : Eqv (add a c) (add b c) := by
  dsimp [Eqv, add] at hab ⊢
  rw [Int.add_mul, Int.add_mul]
  rw [int_mul4 a.num c.den b.den c.den]
  rw [int_mul4 b.num c.den a.den c.den]
  rw [int_mul4 c.num a.den b.den c.den]
  rw [hab]

theorem add_eqv_add {a b c d : Q} (hab : Eqv a b) (hcd : Eqv c d) : Eqv (add a c) (add b d) := by
  have h1 : Eqv (add a c) (add b c) := add_eqv_add_right hab
  have h2 : Eqv (add c b) (add d b) := add_eqv_add_right hcd
  have h3 : Eqv (add b c) (add b d) :=
    eqv_trans (add_comm_eqv b c) (eqv_trans h2 (add_comm_eqv d b))
  exact eqv_trans h1 h3

theorem mul_le_mul_right {a b c : Q} (hab : LE a b) (hc : LE zero c) : LE (mul a c) (mul b c) := by
  have hc' : 0 ≤ c.num := nonneg_iff.mp hc
  dsimp [LE, mul] at hab ⊢
  rw [int_mul4 a.num c.num b.den c.den]
  rw [int_mul4 b.num c.num a.den c.den]
  have hcd : 0 ≤ c.num * c.den := int_mul_nonneg hc' (by have := c.den_pos; omega)
  exact int_mul_le_mul_right hab hcd

theorem mul_le_mul_left {a b c : Q} (hab : LE a b) (hc : LE zero c) : LE (mul c a) (mul c b) :=
  le_trans (le_of_eqv (mul_comm_eqv c a))
    (le_trans (mul_le_mul_right hab hc) (le_of_eqv (mul_comm_eqv b c)))

theorem mul_eqv_mul_right {a b c : Q} (hab : Eqv a b) : Eqv (mul a c) (mul b c) := by
  dsimp [Eqv, mul] at hab ⊢
  rw [int_mul4 a.num c.num b.den c.den]
  rw [int_mul4 b.num c.num a.den c.den]
  rw [hab]

theorem mul_eqv_mul {a b c d : Q} (hab : Eqv a b) (hcd : Eqv c d) : Eqv (mul a c) (mul b d) := by
  have h1 : Eqv (mul a c) (mul b c) := mul_eqv_mul_right hab
  have h2 : Eqv (mul c b) (mul d b) := mul_eqv_mul_right hcd
  have h3 : Eqv (mul b c) (mul b d) :=
    eqv_trans (mul_comm_eqv b c) (eqv_trans h2 (mul_comm_eqv d b))
  exact eqv_trans h1 h3

theorem le_of_mul_le_mul_right {a b c : Q} (h : LE (mul a c) (mul b c)) (hc : LT zero c) : LE a b := by
  have hc' : 0 < c.num := pos_iff.mp hc
  dsimp [LE, mul] at h ⊢
  rw [int_mul4 a.num c.num b.den c.den] at h
  rw [int_mul4 b.num c.num a.den c.den] at h
  exact int_le_of_mul_right h (int_mul_pos hc' c.den_pos)

theorem lt_of_mul_lt_mul_right {a b c : Q} (h : LT (mul a c) (mul b c)) (hc : LT zero c) : LT a b := by
  have hc' : 0 < c.num := pos_iff.mp hc
  dsimp [LT, mul] at h ⊢
  rw [int_mul4 a.num c.num b.den c.den] at h
  rw [int_mul4 b.num c.num a.den c.den] at h
  exact int_lt_of_mul_right h (int_mul_pos hc' c.den_pos)

theorem sub_one_le_of_le_one_add {a b : Q} (h : LE a (add one b)) : LE (sub a one) b := by
  simp only [LE, sub, add, one, Int.one_mul, Int.mul_one] at h ⊢
  rw [Int.add_mul] at h
  rw [Int.sub_mul, Int.mul_comm a.den b.den]
  omega

theorem mul_pos {a b : Q} (ha : LT zero a) (hb : LT zero b) : LT zero (mul a b) := by
  rw [pos_iff] at ha hb ⊢
  exact int_mul_pos ha hb

theorem mul_nonneg {a b : Q} (ha : LE zero a) (hb : LE zero b) : LE zero (mul a b) := by
  rw [nonneg_iff] at ha hb ⊢
  exact int_mul_nonneg ha hb

theorem pow_pos {a : Q} (ha : LT zero a) : ∀ k : Nat, LT zero (pow a k)
  | 0 => by dsimp [pow, LT, zero, one]; decide
  | k + 1 => mul_pos (pow_pos ha k) ha

theorem pow_nonneg {a : Q} (ha : LE zero a) : ∀ k : Nat, LE zero (pow a k)
  | 0 => by dsimp [pow, LE, zero, one]; decide
  | k + 1 => mul_nonneg (pow_nonneg ha k) ha

theorem half_add_half (x : Q) : Eqv (add (mul x half) (mul x half)) x := by
  simp only [Eqv, add, mul, half, Int.mul_one]
  calc
    (x.num * (x.den * 2) + x.num * (x.den * 2)) * x.den
        = x.num * (x.den * 2) * x.den + x.num * (x.den * 2) * x.den := by rw [Int.add_mul]
    _   = x.num * (x.den * 2) * (x.den + x.den) := by rw [← Int.mul_add]
    _   = x.num * (x.den * 2) * (x.den * 2) := by
            have h2 : x.den + x.den = x.den * 2 := by omega
            rw [h2]
    _   = x.num * ((x.den * 2) * (x.den * 2)) := by rw [Int.mul_assoc]

/-! ### Desigualdades constructivas tipo Bernoulli (decaimiento y crecimiento) -/

private theorem bernoulli_step_int {d a m : Int} (ha : 0 ≤ a) (hm : 0 ≤ m) :
    (d - a) * (d + (m + 1) * a) ≤ (d + m * a) * d := by
  have hsq : 0 ≤ a * a := int_mul_nonneg ha ha
  have hpen : 0 ≤ (m + 1) * (a * a) := int_mul_nonneg (by omega : 0 ≤ m + 1) hsq
  have hid : (d - a) * (d + (m + 1) * a) = (d + m * a) * d - (m + 1) * (a * a) := by
    calc
      (d - a) * (d + (m + 1) * a)
          = d * (d + (m + 1) * a) - a * (d + (m + 1) * a) := by rw [Int.sub_mul]
      _   = (d * d + d * ((m + 1) * a)) - (a * d + a * ((m + 1) * a)) := by
              rw [Int.mul_add, Int.mul_add]
      _   = (d * d + (m * a * d + a * d)) - (a * d + (m + 1) * (a * a)) := by
              have h1 : d * ((m + 1) * a) = m * a * d + a * d := by
                rw [Int.add_mul, Int.one_mul, Int.mul_add, Int.mul_comm d (m * a), Int.mul_comm d a]
              have h2 : a * ((m + 1) * a) = (m + 1) * (a * a) := by
                rw [← Int.mul_assoc, Int.mul_comm a (m + 1), Int.mul_assoc]
              rw [h1, h2]
      _   = (d * d + m * a * d) - (m + 1) * (a * a) := by omega
      _   = (d + m * a) * d - (m + 1) * (a * a) := by rw [← Int.add_mul]
  omega

private theorem bernoulli_step_factor (p : Q) (hp0 : LE zero p) (k : Nat) :
    LE
      (mul (sub one p) (add one (mul (ofNat (k + 1)) p)))
      (add one (mul (ofNat k) p)) := by
  have ha : 0 ≤ p.num := nonneg_iff.mp hp0
  have hd : 0 < p.den := p.den_pos
  have hk : Int.ofNat (k + 1) = Int.ofNat k + 1 := Int.natCast_add k 1
  have hm : 0 ≤ Int.ofNat k := Int.natCast_nonneg k
  simp only [LE, mul, sub, add, one, ofNat, Int.one_mul, Int.mul_one]
  rw [hk]
  have hstep := bernoulli_step_int (d := p.den) ha hm
  have hmul := int_mul_le_mul_right (c := p.den) hstep (by omega : 0 ≤ p.den)
  rw [Int.mul_assoc (p.den + Int.ofNat k * p.num) p.den p.den] at hmul
  exact hmul

/-- Para `0 ≤ p ≤ 1` y todo `k`, se cumple `(1 - p)^k * (1 + k * p) ≤ 1`. -/
theorem one_sub_pow_mul_le_one (p : Q) (hp0 : LE zero p) (hp1 : LE p one) :
    ∀ k : Nat, LE (mul (pow (sub one p) k) (add one (mul (ofNat k) p))) one
  | 0 => by
      simp only [LE, mul, add, pow, one, ofNat, Int.one_mul, Int.mul_one]
      have h0 : Int.ofNat 0 * p.num = 0 := Int.zero_mul p.num
      rw [h0]
      omega
  | k + 1 => by
      have hsub : LE zero (sub one p) := by
        rw [nonneg_iff]
        dsimp [LE, one] at hp1
        dsimp [sub, one]
        omega
      have hpow : LE zero (pow (sub one p) k) := pow_nonneg hsub k
      have hstep := bernoulli_step_factor p hp0 k
      have hleft := mul_le_mul_left hstep hpow
      have hassoc := le_of_eqv (mul_assoc_eqv (pow (sub one p) k) (sub one p)
        (add one (mul (ofNat (k + 1)) p)))
      have ih := one_sub_pow_mul_le_one p hp0 hp1 k
      exact le_trans hassoc (le_trans hleft ih)

/-- Testigo explícito determinista: para `0 < p < 1` y `L > 0`,
    `(1 - p)^(L.den * p.den) < L`. -/
theorem pow_lt_of_witness (p L : Q) (hp0 : LT zero p) (hp1 : LT p one) (hL : LT zero L) :
    LT (pow (sub one p) (L.den * p.den).toNat) L := by
  let k : Nat := (L.den * p.den).toNat
  have hbd_pos : 0 < L.den * p.den := int_mul_pos L.den_pos p.den_pos
  have hk_eq : Int.ofNat k = L.den * p.den := int_ofNat_toNat (by omega)
  have hLp : 0 < L.num := pos_iff.mp hL
  have hpp : 0 < p.num := pos_iff.mp hp0
  let F : Q := add one (mul (ofNat k) p)
  have hF_pos : LT zero F := by
    rw [pos_iff]
    simp only [F, add, mul, one, ofNat, Int.one_mul, Int.mul_one]
    have hmul_nn : 0 ≤ Int.ofNat k * p.num := int_mul_nonneg (Int.natCast_nonneg k) (by omega)
    have hd : 0 < p.den := p.den_pos
    omega
  have h_one_lt : LT one (mul L F) := by
    simp only [LT, mul, F, add, one, ofNat, Int.one_mul, Int.mul_one]
    rw [hk_eq]
    have h1 : L.den * p.den ≤ (L.den * p.den) * p.num := by
      have := int_mul_le_mul_left (c := L.den * p.den) (a := 1) (b := p.num) (by omega) (by omega)
      rw [Int.mul_one] at this
      exact this
    have h2 : L.den * p.den < p.den + (L.den * p.den) * p.num := by
      have := p.den_pos
      omega
    have h3 : 1 * (p.den + (L.den * p.den) * p.num) ≤ L.num * (p.den + (L.den * p.den) * p.num) :=
      int_mul_le_mul_right (c := p.den + (L.den * p.den) * p.num) (by omega : 1 ≤ L.num) (by omega)
    rw [Int.one_mul] at h3
    omega
  have h_bern : LE (mul (pow (sub one p) k) F) one :=
    one_sub_pow_mul_le_one p (le_of_lt hp0) (le_of_lt hp1) k
  have h_chain : LT (mul (pow (sub one p) k) F) (mul L F) :=
    lt_of_le_of_lt h_bern h_one_lt
  exact lt_of_mul_lt_mul_right h_chain hF_pos

/-- Testigo existencial: para `0 < p < 1` y `L > 0`, existe `k` finito con `(1 - p)^k < L`. -/
theorem exists_pow_lt (p L : Q) (hp0 : LT zero p) (hp1 : LT p one) (hL : LT zero L) :
    ∃ k : Nat, LT (pow (sub one p) k) L :=
  ⟨(L.den * p.den).toNat, pow_lt_of_witness p L hp0 hp1 hL⟩

private theorem rev_bernoulli_step_int {d a m : Int} (ha : 0 ≤ a) (hm : 0 ≤ m) :
    (d + a) * (d - (m + 1) * a) ≤ (d - m * a) * d := by
  have hsq : 0 ≤ a * a := int_mul_nonneg ha ha
  have hpen : 0 ≤ (m + 1) * (a * a) := int_mul_nonneg (by omega : 0 ≤ m + 1) hsq
  have hid : (d + a) * (d - (m + 1) * a) = (d - m * a) * d - (m + 1) * (a * a) := by
    calc
      (d + a) * (d - (m + 1) * a)
          = d * (d - (m + 1) * a) + a * (d - (m + 1) * a) := by rw [Int.add_mul]
      _   = (d * d - d * ((m + 1) * a)) + (a * d - a * ((m + 1) * a)) := by
              rw [int_mul_sub, int_mul_sub]
      _   = (d * d - (m * a * d + a * d)) + (a * d - (m + 1) * (a * a)) := by
              have h1 : d * ((m + 1) * a) = m * a * d + a * d := by
                rw [Int.add_mul, Int.one_mul, Int.mul_add, Int.mul_comm d (m * a), Int.mul_comm d a]
              have h2 : a * ((m + 1) * a) = (m + 1) * (a * a) := by
                rw [← Int.mul_assoc, Int.mul_comm a (m + 1), Int.mul_assoc]
              rw [h1, h2]
      _   = (d * d - m * a * d) - (m + 1) * (a * a) := by omega
      _   = (d - m * a) * d - (m + 1) * (a * a) := by rw [← Int.sub_mul]
  omega

private theorem rev_bernoulli_step_factor (x : Q) (hx0 : LE zero x) (k : Nat) :
    LE
      (mul (add one x) (sub one (mul (ofNat (k + 1)) x)))
      (sub one (mul (ofNat k) x)) := by
  have ha : 0 ≤ x.num := nonneg_iff.mp hx0
  have hd : 0 < x.den := x.den_pos
  have hk : Int.ofNat (k + 1) = Int.ofNat k + 1 := Int.natCast_add k 1
  have hm : 0 ≤ Int.ofNat k := Int.natCast_nonneg k
  simp only [LE, mul, sub, add, one, ofNat, Int.one_mul, Int.mul_one]
  rw [hk]
  have hstep := rev_bernoulli_step_int (d := x.den) ha hm
  have hmul := int_mul_le_mul_right (c := x.den) hstep (by omega : 0 ≤ x.den)
  rw [Int.mul_assoc (x.den - Int.ofNat k * x.num) x.den x.den] at hmul
  exact hmul

/-- Desigualdad espejo de Bernoulli: para todo `x ≥ 0` y todo `k`,
    `(1 + x)^k * (1 - k * x) ≤ 1`. -/
theorem one_add_pow_mul_le_one (x : Q) (hx0 : LE zero x) :
    ∀ k : Nat, LE (mul (pow (add one x) k) (sub one (mul (ofNat k) x))) one
  | 0 => by
      simp only [LE, mul, sub, pow, one, ofNat, Int.one_mul, Int.mul_one]
      have h0 : Int.ofNat 0 * x.num = 0 := Int.zero_mul x.num
      rw [h0]
      omega
  | k + 1 => by
      have hadd : LE zero (add one x) := by
        rw [nonneg_iff]
        have hx' : 0 ≤ x.num := nonneg_iff.mp hx0
        have hd : 0 < x.den := x.den_pos
        simp only [add, one, Int.one_mul, Int.mul_one]
        omega
      have hpow : LE zero (pow (add one x) k) := pow_nonneg hadd k
      have hstep := rev_bernoulli_step_factor x hx0 k
      have hleft := mul_le_mul_left hstep hpow
      have hassoc := le_of_eqv (mul_assoc_eqv (pow (add one x) k) (add one x)
        (sub one (mul (ofNat (k + 1)) x)))
      have ih := one_add_pow_mul_le_one x hx0 k
      exact le_trans hassoc (le_trans hleft ih)

/-- Cota lineal exacta para el crecimiento de producto (usada en `χ²_k`):
    si `x ≥ 0` y `2 k x ≤ 1`, entonces `(1 + x)^k - 1 ≤ 2 k x`. -/
theorem pow_one_add_sub_one_le_two_mul {x : Q} {k : Nat} (hx0 : LE zero x)
    (hsmall : LE (mul (ofInt 2) (mul (ofNat k) x)) one) :
    LE (sub (pow (add one x) k) one) (mul (ofInt 2) (mul (ofNat k) x)) := by
  let y : Q := mul (ofNat k) x
  have hy0 : LE zero y := mul_nonneg (nonneg_iff.mpr (Int.natCast_nonneg k)) hx0
  have hy_num_nn : 0 ≤ y.num := nonneg_iff.mp hy0
  have h2y_le : 2 * y.num ≤ y.den := by
    simp only [LE, mul, ofInt, one, Int.one_mul, Int.mul_one] at hsmall
    exact hsmall
  have hsub_pos : LT zero (sub one y) := by
    rw [pos_iff]
    simp only [sub, one, Int.one_mul, Int.mul_one]
    have hd : 0 < y.den := y.den_pos
    omega
  have h1 : LE (mul (pow (add one x) k) (sub one y)) one :=
    one_add_pow_mul_le_one x hx0 k
  have h2 : LE one (mul (add one (mul (ofInt 2) y)) (sub one y)) := by
    simp only [LE, one, mul, add, sub, ofInt, Int.one_mul, Int.mul_one]
    have hrem : 0 ≤ y.num * (y.den - 2 * y.num) := int_mul_nonneg hy_num_nn (by omega)
    have hid :
        (y.den + 2 * y.num) * (y.den - y.num) = y.den * y.den + y.num * (y.den - 2 * y.num) := by
      calc
        (y.den + 2 * y.num) * (y.den - y.num)
            = y.den * (y.den - y.num) + 2 * y.num * (y.den - y.num) := by rw [Int.add_mul]
        _   = (y.den * y.den - y.den * y.num) + (2 * y.num * y.den - 2 * y.num * y.num) := by
                rw [int_mul_sub, int_mul_sub]
        _   = (y.den * y.den - y.num * y.den) + (2 * (y.num * y.den) - 2 * (y.num * y.num)) := by
                rw [Int.mul_comm y.den y.num, Int.mul_assoc 2 y.num y.den, Int.mul_assoc 2 y.num y.num]
        _   = y.den * y.den + (y.num * y.den - y.num * (2 * y.num)) := by
                have h2a : y.num * (2 * y.num) = 2 * (y.num * y.num) := by
                  rw [← Int.mul_assoc, Int.mul_comm y.num 2, Int.mul_assoc]
                rw [h2a]
                omega
        _   = y.den * y.den + y.num * (y.den - 2 * y.num) := by rw [← int_mul_sub]
    omega
  have hprod : LE (mul (pow (add one x) k) (sub one y))
      (mul (add one (mul (ofInt 2) y)) (sub one y)) := le_trans h1 h2
  have hP_le : LE (pow (add one x) k) (add one (mul (ofInt 2) y)) :=
    le_of_mul_le_mul_right hprod hsub_pos
  exact sub_one_le_of_le_one_add hP_le

end Q

/-! ============================================================================
    SECCIÓN 3. FIBRAS BUENAS, DIVERGENCIA χ² Y GENEALOGÍA DE `decodingMass`
    (SECCIONES 5, 6, 7 Y 16 DEL MANUSCRITO)
    ============================================================================ -/

/-- Cota uniforme de masa de fibras buenas `g₀ = 10 η² 2^(-l r_s)` (Sección 5.1). -/
def goodFiberMass (η : Q) (l r_s : Nat) : Q :=
  ⟨10 * (η.num * η.num),
   pow2Int (l * r_s) * (η.den * η.den),
   int_mul_pos (pow2Int_pos (l * r_s)) (int_mul_pos η.den_pos η.den_pos)⟩

theorem goodFiberMass_pos {η : Q} (hη : Q.LT Q.zero η) (l r_s : Nat) :
    Q.LT Q.zero (goodFiberMass η l r_s) := by
  rw [Q.pos_iff] at hη ⊢
  dsimp [goodFiberMass]
  exact int_mul_pos (by decide) (int_mul_pos hη hη)

/-- Divergencia χ² por bloque singleton respecto de la uniforme: `(n - 1) / 3` (Sección 6). -/
def chiSqBlock (n : Nat) : Q :=
  Q.mkPos (Int.ofNat n - 1) 3 (by decide)

/-- Cálculo explícito de `n² · (1/n² + 3(n - 1) / (9 n²)) - 1` para un bloque singleton. -/
def singletonChiSqExpanded (n : Nat) (hn : 1 ≤ n) : Q :=
  let N : Int := Int.ofNat n
  have hN_pos : 0 < N := Int.natCast_pos.mpr (by omega)
  have hS_pos : 0 < N * N := int_mul_pos hN_pos hN_pos
  have h9S_pos : 0 < 9 * (N * N) := int_mul_pos (by decide) hS_pos
  let p00_sq : Q := Q.mkPos 1 (N * N) hS_pos
  let p_nz_sum_sq : Q := Q.mkPos (3 * (N - 1)) (9 * (N * N)) h9S_pos
  Q.sub (Q.mul (Q.ofInt (N * N)) (Q.add p00_sq p_nz_sum_sq)) Q.one

/-- Derivación desde primeros principios de la divergencia χ² por bloque:
    `n² · (1/n² + 3(n - 1)/(9 n²)) - 1 = (n - 1) / 3` para todo `n ≥ 1`. -/
theorem singleton_chiSq_exact (n : Nat) (hn : 1 ≤ n) :
    Q.Eqv (singletonChiSqExpanded n hn) (chiSqBlock n) := by
  simp only [Q.Eqv, singletonChiSqExpanded, chiSqBlock, Q.sub, Q.mul, Q.add, Q.ofInt, Q.one,
    Q.mkPos, Int.one_mul, Int.mul_one]
  let N : Int := Int.ofNat n
  let S : Int := N * N
  show (S * (9 * S + 3 * (N - 1) * S) - S * (9 * S)) * 3 = (N - 1) * (S * (9 * S))
  have hstep : S * (9 * S + 3 * (N - 1) * S) - S * (9 * S) = S * (3 * (N - 1) * S) := by
    rw [Int.mul_add]
    omega
  rw [hstep]
  have h9 : (3 : Int) * 3 = 9 := by decide
  calc
    S * (3 * (N - 1) * S) * 3
        = S * (3 * (N - 1) * S * 3) := by rw [Int.mul_assoc]
    _   = S * (3 * (N - 1) * (S * 3)) := by rw [Int.mul_assoc (3 * (N - 1)) S 3]
    _   = S * (3 * (N - 1) * (3 * S)) := by rw [Int.mul_comm S 3]
    _   = S * ((3 * 3) * ((N - 1) * S)) := by rw [int_mul4 3 (N - 1) 3 S]
    _   = S * (9 * ((N - 1) * S)) := by rw [h9]
    _   = S * ((N - 1) * (9 * S)) := by
            congr 1
            rw [← Int.mul_assoc, Int.mul_comm 9 (N - 1), Int.mul_assoc]
    _   = (N - 1) * (S * (9 * S)) := by
            rw [← Int.mul_assoc, Int.mul_comm S (N - 1), Int.mul_assoc]

/-- Divergencia χ² acumulada sobre `k` bloques independientes: `(1 + ((n - 1)/3) β²)^k - 1`. -/
def chiSqTotal (n k : Nat) (β : Q) : Q :=
  Q.sub (Q.pow (Q.add Q.one (Q.mul (chiSqBlock n) (Q.mul β β))) k) Q.one

/-- Masa visible transferida `γ₁ = α g₀ / (8 · 2^(l r_s))` (Sección 6). -/
def visibleMass (α g₀ : Q) (l r_s : Nat) : Q :=
  ⟨α.num * g₀.num,
   8 * pow2Int (l * r_s) * (α.den * g₀.den),
   int_mul_pos (int_mul_pos (by decide) (pow2Int_pos (l * r_s))) (int_mul_pos α.den_pos g₀.den_pos)⟩

/-- Masa condicional de decodificación Fourier `2^(-l r_s) · (α / 8)² · 2^(-r_s)` (Sección 7). -/
def conditionalMass (α : Q) (l r_s : Nat) : Q :=
  ⟨α.num * α.num,
   64 * pow2Int (l * r_s + r_s) * (α.den * α.den),
   int_mul_pos (int_mul_pos (by decide) (pow2Int_pos (l * r_s + r_s)))
     (int_mul_pos α.den_pos α.den_pos)⟩

/-- Masa inferior decodificada global `L = α³ g₀ / (512 · 2^(2 l r_s + r_s))` (Secciones 7, 11, 14). -/
def decodingMass (α g₀ : Q) (l r_s : Nat) : Q :=
  ⟨α.num * α.num * α.num * g₀.num,
   512 * pow2Int (2 * (l * r_s) + r_s) * (α.den * α.den * α.den * g₀.den),
   int_mul_pos (int_mul_pos (by decide) (pow2Int_pos (2 * (l * r_s) + r_s)))
     (int_mul_pos (int_mul_pos (int_mul_pos α.den_pos α.den_pos) α.den_pos) g₀.den_pos)⟩

/-- Hallazgo 3 (Sección 16): `visibleMass * conditionalMass` coincide exactamente con `decodingMass`. -/
theorem decodingMass_genealogy (α g₀ : Q) (l r_s : Nat) :
    Q.Eqv (Q.mul (visibleMass α g₀ l r_s) (conditionalMass α l r_s)) (decodingMass α g₀ l r_s) := by
  dsimp [Q.Eqv, Q.mul, visibleMass, conditionalMass, decodingMass]
  have hnum : (α.num * g₀.num) * (α.num * α.num) = α.num * α.num * α.num * g₀.num := by
    calc
      (α.num * g₀.num) * (α.num * α.num)
          = (α.num * α.num) * (g₀.num * α.num) := int_mul4 α.num g₀.num α.num α.num
      _   = (α.num * α.num) * (α.num * g₀.num) := by rw [Int.mul_comm g₀.num α.num]
      _   = α.num * α.num * α.num * g₀.num := by rw [← Int.mul_assoc]
  have hden_a : (α.den * g₀.den) * (α.den * α.den) = α.den * α.den * α.den * g₀.den := by
    calc
      (α.den * g₀.den) * (α.den * α.den)
          = (α.den * α.den) * (g₀.den * α.den) := int_mul4 α.den g₀.den α.den α.den
      _   = (α.den * α.den) * (α.den * g₀.den) := by rw [Int.mul_comm g₀.den α.den]
      _   = α.den * α.den * α.den * g₀.den := by rw [← Int.mul_assoc]
  have hexp : l * r_s + (l * r_s + r_s) = 2 * (l * r_s) + r_s := by omega
  have h512 : (8 : Int) * 64 = 512 := by decide
  have hden_p : (8 * pow2Int (l * r_s)) * (64 * pow2Int (l * r_s + r_s)) =
      512 * pow2Int (2 * (l * r_s) + r_s) := by
    rw [int_mul4 8 (pow2Int (l * r_s)) 64 (pow2Int (l * r_s + r_s))]
    rw [h512, ← pow2Int_add (l * r_s) (l * r_s + r_s), hexp]
  have hden :
      (8 * pow2Int (l * r_s) * (α.den * g₀.den)) * (64 * pow2Int (l * r_s + r_s) * (α.den * α.den)) =
      512 * pow2Int (2 * (l * r_s) + r_s) * (α.den * α.den * α.den * g₀.den) := by
    rw [int_mul4 (8 * pow2Int (l * r_s)) (α.den * g₀.den)
      (64 * pow2Int (l * r_s + r_s)) (α.den * α.den)]
    rw [hden_p, hden_a]
  rw [hnum, hden]

theorem decodingMass_pos {α g₀ : Q} (hα : Q.LT Q.zero α) (hg : Q.LT Q.zero g₀) (l r_s : Nat) :
    Q.LT Q.zero (decodingMass α g₀ l r_s) := by
  rw [Q.pos_iff] at hα hg ⊢
  dsimp [decodingMass]
  exact int_mul_pos (int_mul_pos (int_mul_pos hα hα) hα) hg

theorem decodingMass_eq_zero_of_g0_zero (α : Q) {g₀ : Q} (hg : Q.Eqv g₀ Q.zero) (l r_s : Nat) :
    Q.Eqv (decodingMass α g₀ l r_s) Q.zero := by
  dsimp [Q.Eqv, Q.zero] at hg
  have hg0 : g₀.num = 0 := by
    rw [Int.mul_one, Int.zero_mul] at hg
    exact hg
  dsimp [Q.Eqv, Q.zero, decodingMass]
  rw [hg0, Int.mul_zero, Int.zero_mul, Int.zero_mul]

/-! ============================================================================
    SECCIÓN 4. COORDENADAS LIMPIAS, `D(k)` Y RÉGIMEN ACOPLADO `k = m³, β = 1/m²`
    (SECCIONES 6, 8 Y 9 DEL MANUSCRITO)
    ============================================================================ -/

/-- Probabilidad de coordenada limpia `p_A = β · 2^(-dim W - r)` (Sección 8). -/
def cleanProb (β : Q) (dimW r : Nat) : Q :=
  ⟨β.num,
   pow2Int (dimW + r) * β.den,
   int_mul_pos (pow2Int_pos (dimW + r)) β.den_pos⟩

/-- Monotonicidad de `p_A`: si `rank A ≤ r_s` y `β ≥ 0`, entonces
    `β · 2^(-dim W - r_s) ≤ β · 2^(-dim W - rank A)`. -/
theorem cleanProb_monotone_rank {β : Q} (hβ : Q.LE Q.zero β)
    (dimW rankA r_s : Nat) (hrank : rankA ≤ r_s) :
    Q.LE (cleanProb β dimW r_s) (cleanProb β dimW rankA) := by
  have hβ' : 0 ≤ β.num := Q.nonneg_iff.mp hβ
  have hpow : pow2Int (dimW + rankA) ≤ pow2Int (dimW + r_s) :=
    pow2Int_mono (by omega)
  dsimp [Q.LE, cleanProb]
  have hden : pow2Int (dimW + rankA) * β.den ≤ pow2Int (dimW + r_s) * β.den :=
    int_mul_le_mul_right (c := β.den) hpow (by have := β.den_pos; omega)
  exact int_mul_le_mul_left hden hβ'

/-- Probabilidad efectiva por paso `p = β / (3600 · 2^(dim W + r_s))`. -/
def cleanProbLower (β : Q) (dimW r_s : Nat) : Q :=
  ⟨β.num,
   3600 * pow2Int (dimW + r_s) * β.den,
   int_mul_pos (int_mul_pos (by decide) (pow2Int_pos (dimW + r_s))) β.den_pos⟩

/-- Base de decaimiento `1 - β / (3600 · 2^(dim W + r_s))`. -/
def cleanDecayStep (β : Q) (dimW r_s : Nat) : Q :=
  Q.sub Q.one (cleanProbLower β dimW r_s)

/-- Cota superior por coordenadas limpias `D(k) = (1 - β / (3600 · 2^(dim W + r_s)))^k`. -/
def fullSeedAgreement_upper (β : Q) (dimW r_s k : Nat) : Q :=
  Q.pow (cleanDecayStep β dimW r_s) k

theorem cleanProbLower_pos {β : Q} (hβ0 : Q.LT Q.zero β) (dimW r_s : Nat) :
    Q.LT Q.zero (cleanProbLower β dimW r_s) := by
  rw [Q.pos_iff] at hβ0 ⊢
  exact hβ0

theorem cleanProbLower_lt_one {β : Q} (hβ1 : Q.LT β Q.one) (dimW r_s : Nat) :
    Q.LT (cleanProbLower β dimW r_s) Q.one := by
  dsimp [Q.LT, Q.one] at hβ1
  dsimp [Q.LT, Q.one, cleanProbLower]
  rw [Int.mul_one, Int.one_mul] at hβ1 ⊢
  have hp : 1 ≤ pow2Int (dimW + r_s) := pow2Int_ge_one (dimW + r_s)
  have h3600 : 1 ≤ 3600 * pow2Int (dimW + r_s) := by omega
  have hmul : 1 * β.den ≤ (3600 * pow2Int (dimW + r_s)) * β.den :=
    int_mul_le_mul_right (c := β.den) h3600 (by have := β.den_pos; omega)
  rw [Int.one_mul] at hmul
  omega

theorem cleanDecayStep_pos {β : Q} (hβ1 : Q.LT β Q.one) (dimW r_s : Nat) :
    Q.LT Q.zero (cleanDecayStep β dimW r_s) := by
  have hlt := cleanProbLower_lt_one hβ1 dimW r_s
  dsimp [Q.LT, Q.one] at hlt
  rw [Q.pos_iff]
  dsimp [cleanDecayStep, Q.sub, Q.one]
  rw [Int.mul_one, Int.one_mul] at hlt ⊢
  omega

/-- Para todo `k` finito y `β < 1`, la cota superior `D(k)` es estrictamente positiva. -/
theorem fullSeedAgreement_upper_pos {β : Q} (hβ1 : Q.LT β Q.one) (dimW r_s k : Nat) :
    Q.LT Q.zero (fullSeedAgreement_upper β dimW r_s k) :=
  Q.pow_pos (cleanDecayStep_pos hβ1 dimW r_s) k

/-- Existencia constructiva de `k` finito con `β` fijo que garantiza `D(k) < L`. -/
theorem exists_k_upper_lt_decodingMass {α g₀ β : Q}
    (hα : Q.LT Q.zero α) (hg : Q.LT Q.zero g₀)
    (hβ0 : Q.LT Q.zero β) (hβ1 : Q.LT β Q.one) (dimW l r_s : Nat) :
    ∃ k : Nat, Q.LT (fullSeedAgreement_upper β dimW r_s k) (decodingMass α g₀ l r_s) :=
  Q.exists_pow_lt
    (cleanProbLower β dimW r_s)
    (decodingMass α g₀ l r_s)
    (cleanProbLower_pos hβ0 dimW r_s)
    (cleanProbLower_lt_one hβ1 dimW r_s)
    (decodingMass_pos hα hg l r_s)

/-! ### Régimen acoplado racional exacto `k = m³`, `β = 1 / m² = k^(-2/3)` -/

/-- Parámetro entero `m = s + 2 ≥ 2` para el régimen acoplado exacto `β = k^(-2/3)`. -/
def coupledM (s : Nat) : Nat := s + 2

/-- Tamaño matricial `k = m³`. -/
def coupledK (s : Nat) : Nat := coupledM s * coupledM s * coupledM s

private theorem coupledM_pos (s : Nat) : 0 < coupledM s := by
  dsimp [coupledM]; omega

/-- Tasa acoplada `β(k) = 1 / m² = k^(-2/3)`. -/
def coupledBeta (s : Nat) : Q :=
  Q.mkPos 1 (Int.ofNat (coupledM s * coupledM s))
    (Int.natCast_pos.mpr (nat_mul_pos_aux (coupledM_pos s) (coupledM_pos s)))

/-- Escala común `1 / m = k^(-1/3)` del punto de balance simétrico `a = 2/3`. -/
def coupledInvM (s : Nat) : Q :=
  Q.mkPos 1 (Int.ofNat (coupledM s)) (Int.natCast_pos.mpr (coupledM_pos s))

theorem coupledBeta_pos (s : Nat) : Q.LT Q.zero (coupledBeta s) := by
  rw [Q.pos_iff]
  dsimp [coupledBeta, Q.mkPos]
  decide

theorem coupledBeta_lt_one (s : Nat) : Q.LT (coupledBeta s) Q.one := by
  dsimp [Q.LT, coupledBeta, Q.mkPos, Q.one]
  have hsq : 1 < coupledM s * coupledM s := by
    dsimp [coupledM]
    rw [Nat.mul_succ, Nat.mul_succ]
    omega
  rw [Int.one_mul, ← Int.natCast_mul]
  exact int_ofNat_lt hsq

/-- Identidad exacta del régimen acoplado: `k · β² = m³ / m⁴ = 1 / m = k^(-1/3)`. -/
theorem coupled_k_beta_sq (s : Nat) :
    Q.Eqv (Q.mul (Q.ofNat (coupledK s)) (Q.mul (coupledBeta s) (coupledBeta s))) (coupledInvM s) := by
  simp only [Q.Eqv, Q.mul, Q.ofNat, coupledK, coupledBeta, coupledInvM, Q.mkPos,
    Int.one_mul, Int.mul_one]
  rw [← int_ofNat_mul, ← int_ofNat_mul]
  rw [Nat.mul_assoc (coupledM s * coupledM s) (coupledM s) (coupledM s)]

/-- Identidad exacta del régimen acoplado: `k · β = m³ / m² = m = k^(1/3)`. -/
theorem coupled_k_beta (s : Nat) :
    Q.Eqv (Q.mul (Q.ofNat (coupledK s)) (coupledBeta s)) (Q.ofNat (coupledM s)) := by
  simp only [Q.Eqv, Q.mul, Q.ofNat, coupledK, coupledBeta, Q.mkPos, Int.one_mul, Int.mul_one]
  rw [← int_ofNat_mul]
  rw [Nat.mul_assoc (coupledM s) (coupledM s) (coupledM s)]

/-- **Teorema de cierre simultáneo del régimen `β = k^(-2/3)` (Secciones 6, 8 y 9)**:
    para cualesquiera `n ≥ 1`, dimensiones `dimW, l, r_s`, masas `α > 0, g₀ > 0` y
    tolerancia `τ > 0` de transferencia χ², existe explícitamente `s` (`m = s + 2`,
    `k = m³`, `β = 1 / m²`) tal que **simultáneamente**:
    - `0 < β < 1`,
    - `k β² = 1/m` y `k β = m`,
    - la divergencia χ² acumulada satisface `chiSqTotal n k β < τ`, y
    - la cota por coordenadas limpias cruza estrictamente `D(k) < decodingMass α g₀ l r_s`. -/
theorem exists_coupled_two_thirds_regime
    (n : Nat) (hn : 1 ≤ n) (dimW l r_s : Nat)
    {α g₀ τ : Q} (hα : Q.LT Q.zero α) (hg : Q.LT Q.zero g₀) (hτ : Q.LT Q.zero τ) :
    ∃ s : Nat,
      Q.LT Q.zero (coupledBeta s) ∧
      Q.LT (coupledBeta s) Q.one ∧
      Q.Eqv (Q.mul (Q.ofNat (coupledK s)) (Q.mul (coupledBeta s) (coupledBeta s))) (coupledInvM s) ∧
      Q.Eqv (Q.mul (Q.ofNat (coupledK s)) (coupledBeta s)) (Q.ofNat (coupledM s)) ∧
      Q.LT (chiSqTotal n (coupledK s) (coupledBeta s)) τ ∧
      Q.LT (fullSeedAgreement_upper (coupledBeta s) dimW r_s (coupledK s)) (decodingMass α g₀ l r_s) := by
  let L : Q := decodingMass α g₀ l r_s
  let C_den : Int := 3600 * pow2Int (dimW + r_s)
  have hC_pos : 0 < C_den := int_mul_pos (by decide) (pow2Int_pos (dimW + r_s))
  have hLC_pos : 0 < L.den * C_den := int_mul_pos L.den_pos hC_pos
  have hτd_nn : 0 ≤ τ.den := by have := τ.den_pos; omega
  have hτd_eq : Int.ofNat τ.den.toNat = τ.den := int_ofNat_toNat hτd_nn
  have hτd_nat_pos : 0 < τ.den.toNat := by
    have hcast : 0 < Int.ofNat τ.den.toNat := by
      rw [hτd_eq]
      exact τ.den_pos
    exact Int.natCast_pos.mp hcast
  let s : Nat := n * τ.den.toNat + (L.den * C_den).toNat
  refine ⟨s, coupledBeta_pos s, coupledBeta_lt_one s, coupled_k_beta_sq s, coupled_k_beta s, ?_, ?_⟩
  · -- Parte 1: Cota de transferencia `chiSqTotal n (coupledK s) (coupledBeta s) < τ`
    let m : Nat := coupledM s
    let k : Nat := coupledK s
    let β : Q := coupledBeta s
    let x : Q := Q.mul (chiSqBlock n) (Q.mul β β)
    have hm_pos : 0 < Int.ofNat m := Int.natCast_pos.mpr (coupledM_pos s)
    have h_ntau_lt_m : n * τ.den.toNat < m := by
      dsimp [m, coupledM, s]
      omega
    have hn_lt_m : n < m := by
      have h1 : n * 1 ≤ n * τ.den.toNat := Nat.mul_le_mul_left n hτd_nat_pos
      rw [Nat.mul_one] at h1
      omega
    have hx0 : Q.LE Q.zero x := by
      rw [Q.nonneg_iff]
      simp only [x, Q.mul, chiSqBlock, β, coupledBeta, Q.mkPos, Int.mul_one]
      have hn1 : 1 ≤ Int.ofNat n := int_ofNat_le hn
      omega
    let kx_simp : Q := Q.mkPos (Int.ofNat n - 1) (3 * Int.ofNat m) (int_mul_pos (by decide) hm_pos)
    have hkx_step1 : Q.Eqv (Q.mul (Q.ofNat k) x) (Q.mul (chiSqBlock n) (Q.mul (Q.ofNat k) (Q.mul β β))) := by
      have ha1 := Q.eqv_symm (Q.mul_assoc_eqv (Q.ofNat k) (chiSqBlock n) (Q.mul β β))
      have ha2 := Q.mul_eqv_mul_right (c := Q.mul β β) (Q.mul_comm_eqv (Q.ofNat k) (chiSqBlock n))
      have ha3 := Q.mul_assoc_eqv (chiSqBlock n) (Q.ofNat k) (Q.mul β β)
      exact Q.eqv_trans ha1 (Q.eqv_trans ha2 ha3)
    have hkx_step2 :
        Q.Eqv (Q.mul (chiSqBlock n) (Q.mul (Q.ofNat k) (Q.mul β β)))
              (Q.mul (chiSqBlock n) (coupledInvM s)) :=
      Q.mul_eqv_mul (Q.eqv_refl (chiSqBlock n)) (coupled_k_beta_sq s)
    have hkx_step3 : Q.Eqv (Q.mul (chiSqBlock n) (coupledInvM s)) kx_simp := by
      simp only [Q.Eqv, Q.mul, chiSqBlock, coupledInvM, kx_simp, m, Q.mkPos, Int.mul_one]
    have hkx_eqv : Q.Eqv (Q.mul (Q.ofNat k) x) kx_simp :=
      Q.eqv_trans hkx_step1 (Q.eqv_trans hkx_step2 hkx_step3)
    have h2kx_eqv : Q.Eqv (Q.mul (Q.ofInt 2) (Q.mul (Q.ofNat k) x)) (Q.mul (Q.ofInt 2) kx_simp) :=
      Q.mul_eqv_mul (Q.eqv_refl (Q.ofInt 2)) hkx_eqv
    have h2kx_le_one : Q.LE (Q.mul (Q.ofInt 2) kx_simp) Q.one := by
      simp only [Q.LE, Q.mul, Q.ofInt, kx_simp, Q.mkPos, Q.one, Int.one_mul, Int.mul_one]
      have hnm : Int.ofNat n < Int.ofNat m := int_ofNat_lt hn_lt_m
      omega
    have hsmall : Q.LE (Q.mul (Q.ofInt 2) (Q.mul (Q.ofNat k) x)) Q.one :=
      Q.le_trans (Q.le_of_eqv h2kx_eqv) h2kx_le_one
    have hchi_le : Q.LE (chiSqTotal n k β) (Q.mul (Q.ofInt 2) (Q.mul (Q.ofNat k) x)) :=
      Q.pow_one_add_sub_one_le_two_mul hx0 hsmall
    have hchi_le' : Q.LE (chiSqTotal n k β) (Q.mul (Q.ofInt 2) kx_simp) :=
      Q.le_trans hchi_le (Q.le_of_eqv h2kx_eqv)
    have h2kx_lt_tau : Q.LT (Q.mul (Q.ofInt 2) kx_simp) τ := by
      simp only [Q.LT, Q.mul, Q.ofInt, kx_simp, Q.mkPos, Int.one_mul]
      have hnm_prod : Int.ofNat n * τ.den < Int.ofNat m := by
        rw [← hτd_eq, ← int_ofNat_mul]
        exact int_ofNat_lt h_ntau_lt_m
      have h1 : (Int.ofNat n - 1) * τ.den < Int.ofNat m := by
        rw [Int.sub_mul, Int.one_mul]
        have := τ.den_pos
        omega
      have hτn : 1 ≤ τ.num := by
        have := Q.pos_iff.mp hτ
        omega
      have h3 : 1 * (3 * Int.ofNat m) ≤ τ.num * (3 * Int.ofNat m) :=
        int_mul_le_mul_right (c := 3 * Int.ofNat m) hτn (by omega)
      rw [Int.one_mul] at h3
      rw [Int.mul_assoc 2 (Int.ofNat n - 1) τ.den]
      omega
    exact Q.lt_of_le_of_lt hchi_le' h2kx_lt_tau
  · -- Parte 2: Separación estricta `fullSeedAgreement_upper (coupledBeta s) dimW r_s (coupledK s) < L`
    let m : Nat := coupledM s
    let k : Nat := coupledK s
    let β : Q := coupledBeta s
    let p : Q := cleanProbLower β dimW r_s
    let F : Q := Q.add Q.one (Q.mul (Q.ofNat k) p)
    have hm_pos : 0 < Int.ofNat m := Int.natCast_pos.mpr (coupledM_pos s)
    have h_LC_lt_m : (L.den * C_den).toNat < m := by
      dsimp [m, coupledM, s]
      omega
    have hp0 : Q.LT Q.zero p := cleanProbLower_pos (coupledBeta_pos s) dimW r_s
    have hp1 : Q.LT p Q.one := cleanProbLower_lt_one (coupledBeta_lt_one s) dimW r_s
    have hbern : Q.LE (Q.mul (fullSeedAgreement_upper β dimW r_s k) F) Q.one :=
      Q.one_sub_pow_mul_le_one p (Q.le_of_lt hp0) (Q.le_of_lt hp1) k
    let kp_simp : Q := Q.mkPos (Int.ofNat m) C_den hC_pos
    have hkp_eqv : Q.Eqv (Q.mul (Q.ofNat k) p) kp_simp := by
      simp only [Q.Eqv, Q.mul, Q.ofNat, k, coupledK, p, cleanProbLower, β, coupledBeta,
        kp_simp, Q.mkPos, Int.one_mul, Int.mul_one]
      have hm3 : Int.ofNat (m * m * m) = Int.ofNat m * Int.ofNat (m * m) := by
        rw [← int_ofNat_mul, Nat.mul_assoc]
      change Int.ofNat (m * m * m) * C_den = Int.ofNat m * (C_den * Int.ofNat (m * m))
      rw [hm3]
      calc
        Int.ofNat m * Int.ofNat (m * m) * C_den
            = Int.ofNat m * (Int.ofNat (m * m) * C_den) := by rw [Int.mul_assoc]
        _   = Int.ofNat m * (C_den * Int.ofNat (m * m)) := by
                rw [Int.mul_comm (Int.ofNat (m * m)) C_den]
    have hF_eqv : Q.Eqv F (Q.add Q.one kp_simp) :=
      Q.add_eqv_add (Q.eqv_refl Q.one) hkp_eqv
    have hF_simp_pos : Q.LT Q.zero (Q.add Q.one kp_simp) := by
      rw [Q.pos_iff]
      simp only [Q.add, Q.one, kp_simp, Q.mkPos, Int.one_mul, Int.mul_one]
      omega
    have hF_pos : Q.LT Q.zero F :=
      Q.lt_of_lt_of_le hF_simp_pos (Q.le_of_eqv (Q.eqv_symm hF_eqv))
    have h_one_lt_simp : Q.LT Q.one (Q.mul L (Q.add Q.one kp_simp)) := by
      simp only [Q.LT, Q.one, Q.mul, Q.add, kp_simp, Q.mkPos, Int.one_mul, Int.mul_one]
      have hLC_eq : Int.ofNat (L.den * C_den).toNat = L.den * C_den := int_ofNat_toNat (by omega)
      have hLC_lt : L.den * C_den < Int.ofNat m := by
        rw [← hLC_eq]
        exact int_ofNat_lt h_LC_lt_m
      have hLn : 1 ≤ L.num := by
        have hpos : 0 < L.num := Q.pos_iff.mp (decodingMass_pos hα hg l r_s)
        omega
      have hmul : 1 * (C_den + Int.ofNat m) ≤ L.num * (C_den + Int.ofNat m) :=
        int_mul_le_mul_right (c := C_den + Int.ofNat m) hLn (by omega)
      rw [Int.one_mul] at hmul
      omega
    have h_LF_eqv : Q.Eqv (Q.mul L (Q.add Q.one kp_simp)) (Q.mul L F) :=
      Q.mul_eqv_mul (Q.eqv_refl L) (Q.eqv_symm hF_eqv)
    have h_one_lt_LF : Q.LT Q.one (Q.mul L F) :=
      Q.lt_of_lt_of_le h_one_lt_simp (Q.le_of_eqv h_LF_eqv)
    have h_chain : Q.LT (Q.mul (fullSeedAgreement_upper β dimW r_s k) F) (Q.mul L F) :=
      Q.lt_of_le_of_lt hbern h_one_lt_LF
    exact Q.lt_of_mul_lt_mul_right h_chain hF_pos

/-! ============================================================================
    SECCIÓN 5. VENTANA DE ESCALAMIENTO Y BALANCES DE `β = k^(-a)` (SECCIÓN 9)
    ============================================================================ -/

/-- Exponente de transferencia `1 - 2a` en `k β² = k^(1 - 2a)`. -/
def transferExp (a : Q) : Q := Q.sub Q.one (Q.mul (Q.ofInt 2) a)

/-- Exponente de coordenadas limpias `1 - a` en `k β = k^(1 - a)`. -/
def cleanExp (a : Q) : Q := Q.sub Q.one a

/-- Exponente del recíproco `(k β)^(-1) = k^(a - 1)`. -/
def invCleanExp (a : Q) : Q := Q.sub a Q.one

/-- Exponente de variación total `TV_k = O(√(k β²)) = O(k^((1 - 2a)/2))`. -/
def tvExp (a : Q) : Q := Q.mul Q.half (transferExp a)

/-- Proposición 9.1: `k β² → 0` y `k β → ∞` si y sólo si `1/2 < a < 1`. -/
theorem scaling_window_iff (a : Q) :
    (Q.LT (transferExp a) Q.zero ∧ Q.LT Q.zero (cleanExp a)) ↔
    (Q.LT Q.half a ∧ Q.LT a Q.one) := by
  simp only [Q.LT, transferExp, cleanExp, Q.sub, Q.mul, Q.one, Q.zero, Q.half, Q.ofInt,
    Int.one_mul, Int.mul_one, Int.zero_mul]
  constructor
  · intro h
    cases h with
    | intro h1 h2 =>
      constructor <;> omega
  · intro h
    cases h with
    | intro h1 h2 =>
      constructor <;> omega

/-- Observación 9.2: `a = 2/3` es el único punto de balance simétrico `1 - 2a = a - 1`. -/
theorem two_thirds_unique_symmetric_balance (a : Q) :
    Q.Eqv (transferExp a) (invCleanExp a) ↔ Q.Eqv a Q.twoThirds := by
  simp only [Q.Eqv, transferExp, invCleanExp, Q.sub, Q.mul, Q.one, Q.ofInt, Q.twoThirds,
    Int.one_mul, Int.mul_one]
  constructor
  · intro h
    have hlin : a.den - 2 * a.num = a.num - a.den := int_eq_of_mul_right h a.den_pos
    omega
  · intro h
    have hlin : a.den - 2 * a.num = a.num - a.den := by omega
    rw [hlin]

theorem two_thirds_in_window : Q.LT Q.half Q.twoThirds ∧ Q.LT Q.twoThirds Q.one := by
  decide

theorem two_thirds_common_rate :
    Q.Eqv (transferExp Q.twoThirds) Q.negOneThird ∧
    Q.Eqv (invCleanExp Q.twoThirds) Q.negOneThird := by
  decide

/-- Observación 9.2 (balance en variación total): `a = 3/4` es el único punto donde
    `(1 - 2a)/2 = a - 1`, dando tasa común `k^(-1/4)`. -/
theorem three_fourths_unique_tv_balance (a : Q) :
    Q.Eqv (tvExp a) (invCleanExp a) ↔ Q.Eqv a Q.threeFourths := by
  simp only [Q.Eqv, tvExp, transferExp, invCleanExp, Q.sub, Q.mul, Q.one, Q.half, Q.ofInt,
    Q.threeFourths, Int.one_mul, Int.mul_one]
  constructor
  · intro h
    rw [← Int.mul_assoc (a.num - a.den) 2 a.den] at h
    have hlin : a.den - 2 * a.num = (a.num - a.den) * 2 := int_eq_of_mul_right h a.den_pos
    omega
  · intro h
    have hlin : a.den - 2 * a.num = (a.num - a.den) * 2 := by omega
    rw [← Int.mul_assoc (a.num - a.den) 2 a.den, hlin]

theorem three_fourths_in_window : Q.LT Q.half Q.threeFourths ∧ Q.LT Q.threeFourths Q.one := by
  decide

theorem three_fourths_common_rate :
    Q.Eqv (tvExp Q.threeFourths) Q.negOneQuarter ∧
    Q.Eqv (invCleanExp Q.threeFourths) Q.negOneQuarter := by
  decide

/-! ============================================================================
    SECCIÓN 6. PROBABILIDAD FINITA, ESPERANZA Y UNIÓN DE LEYES (SECCIÓN 10)
    ============================================================================ -/

/-- Suma exacta de una función racional sobre `Fin n`. -/
def sumFin : {n : Nat} → (Fin n → Q) → Q
  | 0, _ => Q.zero
  | _ + 1, f => Q.add (f ⟨0, Nat.zero_lt_succ _⟩) (sumFin (fun i => f i.succ))

theorem sumFin_congr : {n : Nat} → {f g : Fin n → Q} →
    (∀ i, Q.Eqv (f i) (g i)) → Q.Eqv (sumFin f) (sumFin g)
  | 0, _, _, _ => Q.eqv_refl Q.zero
  | _ + 1, _, _, h =>
      Q.add_eqv_add (h ⟨0, Nat.zero_lt_succ _⟩) (sumFin_congr (fun i => h i.succ))

/-- Distribución de probabilidad exacta sobre un espacio finito `Fin n`. -/
structure FinDist (n : Nat) where
  prob : Fin n → Q
  nonneg : ∀ i, Q.LE Q.zero (prob i)
  sum_one : Q.Eqv (sumFin prob) Q.one

/-- Esperanza exacta `E_{ω ~ μ}[f(ω)]`. -/
def expectation {n : Nat} (μ : FinDist n) (f : Fin n → Q) : Q :=
  sumFin (fun i => Q.mul (μ.prob i) (f i))

/-- Acuerdo bajo la ley proyectada real `A_act = E_{μ_act}[Agr]`. -/
def actualAgreement {n : Nat} (μ_act : FinDist n) (agr : Fin n → Q) : Q :=
  expectation μ_act agr

/-- Acuerdo bajo la semilla completa `A_full = E_{μ_full}[Agr]`. -/
def fullSeedAgreement {n : Nat} (μ_full : FinDist n) (agr : Fin n → Q) : Q :=
  expectation μ_full agr

/-- Costura de carga (Hallazgo 10.1): leyes idénticas producen `A_act = A_full`. -/
theorem noHiddenConditioning_of_same_law {n : Nat}
    (μ_act μ_full : FinDist n) (agr : Fin n → Q)
    (hlaw : ∀ i, Q.Eqv (μ_act.prob i) (μ_full.prob i)) :
    Q.Eqv (actualAgreement μ_act agr) (fullSeedAgreement μ_full agr) :=
  sumFin_congr (fun i => Q.mul_eqv_mul_right (hlaw i))

/-! ============================================================================
    SECCIÓN 7. TEOREMA DE COSTURA GLOBAL `WitnessMassFlow` (SECCIONES 11 Y 14)
    ============================================================================ -/

/-- Estructura formal que empaqueta las cuatro aristas de la contradicción global. -/
structure WitnessMassFlow where
  decodingMass : Q
  actualAgreement : Q
  fullSeedAgreement : Q
  fullSeedAgreement_upper : Q
  lower_bound : Q.LE decodingMass actualAgreement
  noHiddenConditioning : Q.Eqv actualAgreement fullSeedAgreement
  upper_bound : Q.LE fullSeedAgreement fullSeedAgreement_upper
  strict_separation : Q.LT fullSeedAgreement_upper decodingMass

/-- Cierre abstracto de la cadena `L ≤ A_act = A_full ≤ D < L → False`. -/
theorem WitnessMassFlow.contradiction (w : WitnessMassFlow) : False := by
  have h1 : Q.LE w.decodingMass w.fullSeedAgreement :=
    Q.le_trans w.lower_bound (Q.le_of_eqv w.noHiddenConditioning)
  have h2 : Q.LE w.decodingMass w.fullSeedAgreement_upper :=
    Q.le_trans h1 w.upper_bound
  exact Q.not_lt_of_le h2 w.strict_separation

/-- Teorema 11.1 (Principio de flujo de masa) acoplado a leyes y observable `Agr : Ω → [0, 1]`. -/
structure ProbWitnessMassFlow (n : Nat) where
  μ_act : FinDist n
  μ_full : FinDist n
  agr : Fin n → Q
  agr_range : ∀ i, Q.LE Q.zero (agr i) ∧ Q.LE (agr i) Q.one
  L : Q
  D : Q
  lower_bound : Q.LE L (actualAgreement μ_act agr)
  noHiddenConditioning : Q.Eqv (actualAgreement μ_act agr) (fullSeedAgreement μ_full agr)
  upper_bound : Q.LE (fullSeedAgreement μ_full agr) D
  strict_separation : Q.LT D L

def ProbWitnessMassFlow.toWitnessMassFlow {n : Nat} (p : ProbWitnessMassFlow n) : WitnessMassFlow :=
  { decodingMass := p.L
    actualAgreement := actualAgreement p.μ_act p.agr
    fullSeedAgreement := fullSeedAgreement p.μ_full p.agr
    fullSeedAgreement_upper := p.D
    lower_bound := p.lower_bound
    noHiddenConditioning := p.noHiddenConditioning
    upper_bound := p.upper_bound
    strict_separation := p.strict_separation }

theorem ProbWitnessMassFlow.contradiction {n : Nat} (p : ProbWitnessMassFlow n) : False :=
  p.toWitnessMassFlow.contradiction

/-! ============================================================================
    SECCIÓN 8. CONTROLES NEGATIVOS SOBRE EL MICRO-MODELO `Ω = {0,1}²` (SEC. 12)
    Codificación en `Fin 4`:
      0 ↦ (g = 0, c = 0)
      1 ↦ (g = 0, c = 1)
      2 ↦ (g = 1, c = 0)   [único estado con Agr = 1]
      3 ↦ (g = 1, c = 1)
    ============================================================================ -/

/-- Observable de acuerdo del micro-modelo: `Agr(g, c) = 1_{g = 1 ∧ c = 0}`. -/
def microAgr (i : Fin 4) : Q :=
  match i.val with
  | 2 => Q.one
  | _ => Q.zero

theorem microAgr_range : ∀ i : Fin 4, Q.LE Q.zero (microAgr i) ∧ Q.LE (microAgr i) Q.one
  | ⟨0, _⟩ => by dsimp [microAgr]; decide
  | ⟨1, _⟩ => by dsimp [microAgr]; decide
  | ⟨2, _⟩ => by dsimp [microAgr]; decide
  | ⟨3, _⟩ => by dsimp [microAgr]; decide
  | ⟨_ + 4, hv⟩ => by omega

/-- Ley `μ_act` sin proyectar: soportada en `{c = 0}` con `g ~ Bernoulli(1/2)`. -/
def muActUnprojected : FinDist 4 where
  prob := fun i =>
    match i.val with
    | 0 => Q.half
    | 1 => Q.zero
    | 2 => Q.half
    | _ => Q.zero
  nonneg := fun ⟨v, hv⟩ => by
    match v with
    | 0 => dsimp; decide
    | 1 => dsimp; decide
    | 2 => dsimp; decide
    | 3 => dsimp; decide
    | _ + 4 => omega
  sum_one := by decide

/-- Ley `μ_full` proyectada: `g ~ Bernoulli(1/2)` independiente de `c ~ Bernoulli(3/4)`. -/
def muFullProjected : FinDist 4 where
  prob := fun i =>
    match i.val with
    | 0 => Q.eighth
    | 1 => Q.threeEighths
    | 2 => Q.eighth
    | _ => Q.threeEighths
  nonneg := fun ⟨v, hv⟩ => by
    match v with
    | 0 => dsimp; decide
    | 1 => dsimp; decide
    | 2 => dsimp; decide
    | 3 => dsimp; decide
    | _ + 4 => omega
  sum_one := by decide

/-- Distribución uniforme sobre `Ω = {0,1}²`. -/
def muUniform : FinDist 4 where
  prob := fun _ => Q.quarter
  nonneg := fun _ => by decide
  sum_one := by decide

theorem micro_actual_eval : Q.Eqv (actualAgreement muActUnprojected microAgr) Q.half := by
  decide

theorem micro_full_eval : Q.Eqv (fullSeedAgreement muFullProjected microAgr) Q.eighth := by
  decide

theorem micro_uniform_eval : Q.Eqv (actualAgreement muUniform microAgr) Q.quarter := by
  decide

/-- Proposición 12.1: Sin unión de leyes (`A_act ≠ A_full`), `L ≤ A_act`, `A_full ≤ D` y `D < L`
    son simultáneamente realizables en el micro-modelo probabilístico. -/
theorem control_no_law_union :
    ∃ (μ_act μ_full : FinDist 4) (L D : Q),
      ¬ Q.Eqv (actualAgreement μ_act microAgr) (fullSeedAgreement μ_full microAgr) ∧
      Q.LE L (actualAgreement μ_act microAgr) ∧
      Q.LE (fullSeedAgreement μ_full microAgr) D ∧
      Q.LT D L := by
  refine ⟨muActUnprojected, muFullProjected, Q.half, Q.quarter, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Proposición 12.2: Sin separación estricta `D < L`, las desigualdades `L ≤ A_act = A_full ≤ D`
    son realizables con acuerdo estrictamente positivo (`A_act = A_full = 1/4 > 0`). -/
theorem control_strict_separation_needed :
    ∃ (μ : FinDist 4) (L D : Q),
      Q.LT Q.zero (actualAgreement μ microAgr) ∧
      Q.LE L (actualAgreement μ microAgr) ∧
      Q.Eqv (actualAgreement μ microAgr) (fullSeedAgreement μ microAgr) ∧
      Q.LE (fullSeedAgreement μ microAgr) D := by
  refine ⟨muUniform, Q.quarter, Q.quarter, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Proposición 12.3: Si `g₀ = 0`, entonces `L = 0` mientras `D(k) > 0` para todo `k` finito y
    `β < 1`, por lo que ningún `k` finito logra `D(k) < L`. -/
theorem control_positive_mass_needed (α β : Q) (dimW l r_s k : Nat)
    (hβ1 : Q.LT β Q.one) :
    ¬ Q.LT (fullSeedAgreement_upper β dimW r_s k) (decodingMass α Q.zero l r_s) := by
  intro hlt
  have hD_pos : Q.LT Q.zero (fullSeedAgreement_upper β dimW r_s k) :=
    fullSeedAgreement_upper_pos hβ1 dimW r_s k
  have hL_zero : Q.Eqv (decodingMass α Q.zero l r_s) Q.zero :=
    decodingMass_eq_zero_of_g0_zero α (Q.eqv_refl Q.zero) l r_s
  have hD_lt_zero : Q.LT (fullSeedAgreement_upper β dimW r_s k) Q.zero :=
    Q.lt_of_lt_of_le hlt (Q.le_of_eqv hL_zero)
  exact Q.not_lt_of_le (Q.le_of_lt hD_pos) hD_lt_zero

/-! ============================================================================
    SECCIÓN 9. TORRE NO CIRCULAR DE PARÁMETROS `ParameterTower` (SECS. 13 Y 14)
    ============================================================================ -/

/-- Etapa 0: objetivos exteriores `(ε, δ)`. -/
structure OuterTarget where
  eps : Q
  delta : Q
  eps_pos : Q.LT Q.zero eps
  delta_pos : Q.LT Q.zero delta

/-- Etapa 1: `(ε₀, δ₀, t, C)` fijados antes de cualquier parámetro matricial. -/
structure OuterStage (target : OuterTarget) where
  eps0 : Q
  delta0 : Q
  eps0_pos : Q.LT Q.zero eps0
  eps0_le : Q.LE eps0 target.eps
  delta0_pos : Q.LT Q.zero delta0
  delta0_le : Q.LE delta0 target.delta
  t : Nat
  t_pos : 0 < t
  t_outer_decay : Q.LE (Q.pow (Q.sub Q.one (Q.mkPos 1 10240000 (by decide))) t) delta0
  C : Nat
  C_ge_200 : 200 ≤ C
  pStar_le_budget :
    Q.LE (Q.mkPos 1 (Int.ofNat C) (Int.natCast_pos.mpr (by omega)))
      (Q.divPos eps0 (Q.ofNat t) (by dsimp [Q.ofNat]; have := t_pos; omega))

def OuterStage.pStar {target : OuterTarget} (o : OuterStage target) : Q :=
  Q.mkPos 1 (Int.ofNat o.C) (Int.natCast_pos.mpr (by have := o.C_ge_200; omega))

def OuterStage.outerBudget {target : OuterTarget} (o : OuterStage target) : Q :=
  Q.divPos o.eps0 (Q.ofNat o.t) (by dsimp [Q.ofNat]; have := o.t_pos; omega)

/-- Construcción canónica general de `OuterStage` para **cualquier** `(ε, δ) > 0`. -/
def OuterStage.canonical (target : OuterTarget) : OuterStage target :=
  let p_out : Q := Q.mkPos 1 10240000 (by decide)
  let t : Nat := (target.delta.den * 10240000).toNat
  have ht_eq : Int.ofNat t = target.delta.den * 10240000 :=
    int_ofNat_toNat (by have := target.delta.den_pos; omega)
  have ht_pos : 0 < t :=
    Int.natCast_pos.mp (by
      have hcast : 0 < Int.ofNat t := by
        rw [ht_eq]
        have := target.delta.den_pos
        omega
      exact hcast)
  have ht_decay : Q.LE (Q.pow (Q.sub Q.one p_out) t) target.delta :=
    Q.le_of_lt (Q.pow_lt_of_witness p_out target.delta
      (by dsimp [p_out, Q.LT, Q.zero, Q.mkPos]; decide)
      (by dsimp [p_out, Q.LT, Q.one, Q.mkPos]; decide)
      target.delta_pos)
  let C : Nat := 200 + t * target.eps.den.toNat
  { eps0 := target.eps
    delta0 := target.delta
    eps0_pos := target.eps_pos
    eps0_le := Q.le_refl target.eps
    delta0_pos := target.delta_pos
    delta0_le := Q.le_refl target.delta
    t := t
    t_pos := ht_pos
    t_outer_decay := ht_decay
    C := C
    C_ge_200 := by dsimp [C]; omega
    pStar_le_budget := by
      simp only [Q.LE, Q.mkPos, Q.divPos, Q.ofNat, Int.one_mul, Int.mul_one]
      have hed_eq : Int.ofNat target.eps.den.toNat = target.eps.den :=
        int_ofNat_toNat (by have := target.eps.den_pos; omega)
      have hte_le_C : t * target.eps.den.toNat ≤ C := by dsimp [C]; omega
      have h1 : Int.ofNat t * target.eps.den ≤ Int.ofNat C := by
        rw [← hed_eq, ← int_ofNat_mul]
        exact int_ofNat_le hte_le_C
      have hen : 1 ≤ target.eps.num := by
        have := Q.pos_iff.mp target.eps_pos
        omega
      have h2 : 1 * Int.ofNat C ≤ target.eps.num * Int.ofNat C :=
        int_mul_le_mul_right (c := Int.ofNat C) hen (Int.natCast_nonneg C)
      rw [Int.one_mul] at h2
      rw [Int.mul_comm target.eps.den (Int.ofNat t)]
      omega }

theorem OuterStage.nonempty (target : OuterTarget) : Nonempty (OuterStage target) :=
  ⟨OuterStage.canonical target⟩

/-- Etapa 2: parámetros del test matricial, dependientes únicamente de `p_*` (nunca de `ξ`). -/
structure MatrixStage (pStar : Q) where
  l : Nat
  r_s : Nat
  dimW : Nat
  k : Nat
  k_pos : 0 < k
  α : Q
  g₀ : Q
  α_pos : Q.LT Q.zero α
  g0_pos : Q.LT Q.zero g₀

/-- Etapa 3: error de paridad `ξ`, elegido después de fijar `k` en `MatrixStage`. -/
structure ParityStage (eps0 : Q) (t k : Nat) (ht : 0 < t) (hk : 0 < k) where
  xi : Q
  xi_pos : Q.LT Q.zero xi
  xi_lt_hundredth : Q.LT xi (Q.mkPos 1 100 (by decide))
  xi_lt_budget :
    Q.LT xi
      (Q.divPos eps0
        (Q.ofInt (2 * Int.ofNat k * Int.ofNat t))
        (by
          dsimp [Q.ofInt]
          have hk' : 0 < Int.ofNat k := Int.natCast_pos.mpr hk
          have ht' : 0 < Int.ofNat t := Int.natCast_pos.mpr ht
          exact int_mul_pos (int_mul_pos (by decide) hk') ht'))

/-- Construcción canónica de `ParityStage` para cualesquiera `ε₀ > 0`, `t > 0`, `k > 0`. -/
def ParityStage.canonical (eps0 : Q) (heps : Q.LT Q.zero eps0) (t k : Nat)
    (ht : 0 < t) (hk : 0 < k) : ParityStage eps0 t k ht hk :=
  let D_xi : Int := 101 + 2 * Int.ofNat k * Int.ofNat t * eps0.den
  have hk' : 0 < Int.ofNat k := Int.natCast_pos.mpr hk
  have ht' : 0 < Int.ofNat t := Int.natCast_pos.mpr ht
  have h2kt_pos : 0 < 2 * Int.ofNat k * Int.ofNat t := int_mul_pos (int_mul_pos (by decide) hk') ht'
  have hprod_pos : 0 < 2 * Int.ofNat k * Int.ofNat t * eps0.den :=
    int_mul_pos h2kt_pos eps0.den_pos
  have hD_pos : 0 < D_xi := by
    change 0 < 101 + (2 * Int.ofNat k * Int.ofNat t * eps0.den)
    omega
  { xi := Q.mkPos 1 D_xi hD_pos
    xi_pos := by rw [Q.pos_iff]; dsimp [Q.mkPos]; decide
    xi_lt_hundredth := by
      simp only [Q.LT, Q.mkPos, Int.one_mul]
      change 100 < D_xi
      change 100 < 101 + (2 * Int.ofNat k * Int.ofNat t * eps0.den)
      omega
    xi_lt_budget := by
      simp only [Q.LT, Q.mkPos, Q.divPos, Q.ofInt, Int.one_mul, Int.mul_one]
      have hen : 1 ≤ eps0.num := by
        have := Q.pos_iff.mp heps
        omega
      have hmul : 1 * D_xi ≤ eps0.num * D_xi :=
        int_mul_le_mul_right (c := D_xi) hen (by omega)
      rw [Int.one_mul] at hmul
      rw [Int.mul_comm eps0.den (2 * Int.ofNat k * Int.ofNat t)]
      dsimp [D_xi] at hmul ⊢
      omega }

/-- Torre completa de parámetros con orden estricto por tipos dependientes:
    `(ε, δ) ↦ (ε₀, δ₀, t, C) ↦ p_* = C⁻¹ ↦ (l, r_s, dim W, k, α, g₀) ↦ ξ`. -/
structure ParameterTower where
  target : OuterTarget
  outer : OuterStage target
  matrix : MatrixStage outer.pStar
  parity : ParityStage outer.eps0 outer.t matrix.k outer.t_pos matrix.k_pos

/-- Construcción canónica de toda la torre `ParameterTower` a partir de cualquier `(ε, δ) > 0`
    y cualquier elección válida de parámetros matriciales. -/
def ParameterTower.canonical (target : OuterTarget) (l r_s dimW k : Nat) (hk : 0 < k)
    (α g₀ : Q) (hα : Q.LT Q.zero α) (hg : Q.LT Q.zero g₀) : ParameterTower :=
  let o := OuterStage.canonical target
  let m : MatrixStage o.pStar :=
    { l := l, r_s := r_s, dimW := dimW, k := k, k_pos := hk
      α := α, g₀ := g₀, α_pos := hα, g0_pos := hg }
  let p := ParityStage.canonical o.eps0 o.eps0_pos o.t m.k o.t_pos m.k_pos
  { target := target, outer := o, matrix := m, parity := p }

/-- Cota de presupuesto de paridad (Sección 13): `k * ξ + p_* / 2 ≤ ε₀ / t`. -/
theorem ParameterTower.parity_budget_bound (P : ParameterTower) :
    Q.LE
      (Q.add
        (Q.mul (Q.ofNat P.matrix.k) P.parity.xi)
        (Q.mul P.outer.pStar Q.half))
      P.outer.outerBudget := by
  let B : Q := P.outer.outerBudget
  let K : Int := Int.ofNat P.matrix.k
  let T : Int := Int.ofNat P.outer.t
  have hK_pos : 0 < K := Int.natCast_pos.mpr P.matrix.k_pos
  have hT_pos : 0 < T := Int.natCast_pos.mpr P.outer.t_pos
  have h2KT_pos : 0 < 2 * K * T := int_mul_pos (int_mul_pos (by decide) hK_pos) hT_pos
  have hp_half : Q.LE (Q.mul P.outer.pStar Q.half) (Q.mul B Q.half) :=
    Q.mul_le_mul_right P.outer.pStar_le_budget (by decide)
  have hxi_le : Q.LE P.parity.xi (Q.divPos P.outer.eps0 (Q.ofInt (2 * K * T)) h2KT_pos) :=
    Q.le_of_lt P.parity.xi_lt_budget
  have hk_nn : Q.LE Q.zero (Q.ofNat P.matrix.k) :=
    Q.nonneg_iff.mpr (Int.natCast_nonneg P.matrix.k)
  have hkxi_step :
      Q.LE (Q.mul (Q.ofNat P.matrix.k) P.parity.xi)
           (Q.mul (Q.ofNat P.matrix.k) (Q.divPos P.outer.eps0 (Q.ofInt (2 * K * T)) h2KT_pos)) :=
    Q.mul_le_mul_left hxi_le hk_nn
  have hcancel :
      Q.Eqv
        (Q.mul (Q.ofNat P.matrix.k) (Q.divPos P.outer.eps0 (Q.ofInt (2 * K * T)) h2KT_pos))
        (Q.mul B Q.half) := by
    simp only [Q.Eqv, Q.mul, Q.divPos, Q.ofNat, Q.ofInt, Q.half, B, OuterStage.outerBudget,
      Int.mul_one, Int.one_mul]
    show (K * P.outer.eps0.num) * (P.outer.eps0.den * T * 2) =
         P.outer.eps0.num * (P.outer.eps0.den * (2 * K * T))
    calc
      (K * P.outer.eps0.num) * (P.outer.eps0.den * T * 2)
          = (P.outer.eps0.num * K) * (P.outer.eps0.den * T * 2) := by
              rw [Int.mul_comm K P.outer.eps0.num]
      _   = P.outer.eps0.num * (K * (P.outer.eps0.den * T * 2)) := by
              rw [Int.mul_assoc]
      _   = P.outer.eps0.num * (P.outer.eps0.den * (2 * K * T)) := by
              congr 1
              calc
                K * (P.outer.eps0.den * T * 2)
                    = K * (P.outer.eps0.den * (T * 2)) := by
                        rw [Int.mul_assoc P.outer.eps0.den T 2]
                _   = (K * P.outer.eps0.den) * (T * 2) := by
                        rw [← Int.mul_assoc]
                _   = (P.outer.eps0.den * K) * (2 * T) := by
                        rw [Int.mul_comm K P.outer.eps0.den, Int.mul_comm T 2]
                _   = P.outer.eps0.den * (K * (2 * T)) := by
                        rw [Int.mul_assoc]
                _   = P.outer.eps0.den * (2 * K * T) := by
                        rw [← Int.mul_assoc K 2 T, Int.mul_comm K 2]
  have hkxi_half : Q.LE (Q.mul (Q.ofNat P.matrix.k) P.parity.xi) (Q.mul B Q.half) :=
    Q.le_trans hkxi_step (Q.le_of_eqv hcancel)
  have hsum :
      Q.LE
        (Q.add (Q.mul (Q.ofNat P.matrix.k) P.parity.xi) (Q.mul P.outer.pStar Q.half))
        (Q.add (Q.mul B Q.half) (Q.mul B Q.half)) :=
    Q.add_le_add hkxi_half hp_half
  exact Q.le_trans hsum (Q.le_of_eqv (Q.half_add_half B))

/-- Testigo concreto de satisfacibilidad en `(ε, δ) = (1, 1)`. -/
def ParameterTower.exampleWitness : ParameterTower where
  target :=
    { eps := Q.one
      delta := Q.one
      eps_pos := by decide
      delta_pos := by decide }
  outer :=
    { eps0 := Q.one
      delta0 := Q.one
      eps0_pos := by decide
      eps0_le := by decide
      delta0_pos := by decide
      delta0_le := by decide
      t := 1
      t_pos := by decide
      t_outer_decay := by decide
      C := 200
      C_ge_200 := by decide
      pStar_le_budget := by decide }
  matrix :=
    { l := 1
      r_s := 1
      dimW := 1
      k := 1
      k_pos := by decide
      α := Q.half
      g₀ := Q.half
      α_pos := by decide
      g0_pos := by decide }
  parity :=
    { xi := Q.mkPos 1 200 (by decide)
      xi_pos := by decide
      xi_lt_hundredth := by decide
      xi_lt_budget := by decide }

/-! ============================================================================
    SECCIÓN 10. INTERFAZ AUDITABLE DE ENTRADAS IMPORTADAS (LÍMITE 14.1)
    ============================================================================ -/

/-- Paquete transparente de auditoría: separa las cuatro cotas locales importadas
    del desarrollo principal frente al cierre verificado en este archivo. -/
structure SoundnessAuditBundle (n : Nat) where
  tower : ParameterTower
  β : Q
  β_pos : Q.LT Q.zero β
  β_lt_one : Q.LT β Q.one
  μ_act : FinDist n
  μ_full : FinDist n
  agr : Fin n → Q
  agr_range : ∀ i, Q.LE Q.zero (agr i) ∧ Q.LE (agr i) Q.one
  /-- Entrada importada 1 (Secciones 5–7): extracción + transferencia + decodificación Fourier. -/
  h_decoding_lower :
    Q.LE (decodingMass tower.matrix.α tower.matrix.g₀ tower.matrix.l tower.matrix.r_s)
         (actualAgreement μ_act agr)
  /-- Entrada importada 2 (Sección 10): igualdad exacta de distribuciones `μ_act = μ_full`. -/
  h_same_law : ∀ i, Q.Eqv (μ_act.prob i) (μ_full.prob i)
  /-- Entrada importada 3 (Sección 8): cota superior exponencial por coordenadas limpias. -/
  h_clean_upper :
    Q.LE (fullSeedAgreement μ_full agr)
         (fullSeedAgreement_upper β tower.matrix.dimW tower.matrix.r_s tower.matrix.k)
  /-- Entrada importada 4 (Secciones 8–9): régimen asintótico `D(k) < L`. -/
  h_strict_sep :
    Q.LT (fullSeedAgreement_upper β tower.matrix.dimW tower.matrix.r_s tower.matrix.k)
         (decodingMass tower.matrix.α tower.matrix.g₀ tower.matrix.l tower.matrix.r_s)

/-- Teorema de cierre auditado: toda instancia que satisfaga `SoundnessAuditBundle`
    produce contradicción vía `WitnessMassFlow.contradiction`. -/
theorem audit_soundness_contradiction {n : Nat} (B : SoundnessAuditBundle n) : False :=
  let flow : ProbWitnessMassFlow n :=
    { μ_act := B.μ_act
      μ_full := B.μ_full
      agr := B.agr
      agr_range := B.agr_range
      L := decodingMass B.tower.matrix.α B.tower.matrix.g₀ B.tower.matrix.l B.tower.matrix.r_s
      D := fullSeedAgreement_upper B.β B.tower.matrix.dimW B.tower.matrix.r_s B.tower.matrix.k
      lower_bound := B.h_decoding_lower
      noHiddenConditioning := noHiddenConditioning_of_same_law B.μ_act B.μ_full B.agr B.h_same_law
      upper_bound := B.h_clean_upper
      strict_separation := B.h_strict_sep }
  flow.contradiction

end JuegosUnicos

/-! ============================================================================
    VERIFICACIÓN DE AXIOMAS DEL KERNEL
    ============================================================================ -/
#print axioms JuegosUnicos.Q.pow_one_add_sub_one_le_two_mul
#print axioms JuegosUnicos.goodFiberMass_pos
#print axioms JuegosUnicos.singleton_chiSq_exact
#print axioms JuegosUnicos.decodingMass_genealogy
#print axioms JuegosUnicos.cleanProb_monotone_rank
#print axioms JuegosUnicos.exists_k_upper_lt_decodingMass
#print axioms JuegosUnicos.exists_coupled_two_thirds_regime
#print axioms JuegosUnicos.scaling_window_iff
#print axioms JuegosUnicos.two_thirds_unique_symmetric_balance
#print axioms JuegosUnicos.three_fourths_unique_tv_balance
#print axioms JuegosUnicos.WitnessMassFlow.contradiction
#print axioms JuegosUnicos.control_no_law_union
#print axioms JuegosUnicos.control_strict_separation_needed
#print axioms JuegosUnicos.control_positive_mass_needed
#print axioms JuegosUnicos.OuterStage.nonempty
#print axioms JuegosUnicos.ParameterTower.parity_budget_bound
#print axioms JuegosUnicos.audit_soundness_contradiction
