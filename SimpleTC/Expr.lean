import SimpleTC.Ty

inductive Ctx Φ : Type where
| empty : Ctx Φ
| extend : ∀ {k}, Ctx Φ → Ty Φ k → Ctx Φ
deriving Repr, DecidableEq

inductive InCtx {Φ k} : Ctx Φ → Ty Φ k → Type where
| here : ∀ {Γ a}, InCtx (.extend Γ a) a
| there : ∀ {Γ k' a} {b : Ty Φ k'},
    InCtx Γ a →
    InCtx (.extend Γ b) a
deriving Repr

def renameCtx {Φ Φ'} (ρ : TyRenaming Φ Φ') :
    Ctx Φ →
    Ctx Φ'
| .empty => .empty
| .extend Γ a => .extend (renameCtx ρ Γ) (renameTy ρ a)

inductive RawExpr : Type where
| natLit : Nat → RawExpr
| trueLit : RawExpr
| falseLit : RawExpr
| var : Nat → RawExpr
| lam : RawTy → RawExpr → RawExpr
| app : RawExpr → RawExpr → RawExpr
| tyLam : Kind → RawExpr → RawExpr
| tyApp : RawExpr → RawTy → RawExpr
deriving Repr, DecidableEq

inductive Expr : (Φ : KindCtx) → Ctx Φ → Ty Φ .TyKind → Type where
| natLit : ∀ {Φ Γ}, Nat → Expr Φ Γ .NatTy
| trueLit : ∀ {Φ Γ}, Expr Φ Γ .BoolTy
| falseLit : ∀ {Φ Γ}, Expr Φ Γ .BoolTy

| var : ∀ {Φ Γ a},
    InCtx Γ a →
    Expr Φ Γ a

| lam : ∀ {Φ Γ a b},
    Expr Φ (.extend Γ a) b →
    Expr Φ Γ (.FunTy a b)

| app : ∀ {Φ Γ a b},
    Expr Φ Γ (.FunTy a b) →
    Expr Φ Γ a →
    Expr Φ Γ b

| tyLam :
    (k : Kind) →
    ∀ {Φ Γ Γ' a},
    Expr (.extend Φ k) Γ a →
    Γ = renameCtx .there Γ' →
    Expr Φ Γ' (.Forall k a)

| tyApp : ∀ {Φ k Γ a a'},
    Expr Φ Γ (.Forall k a) →
    (b : Ty Φ k) →
    a' = substTy1 a b →
    Expr Φ Γ a'
deriving Repr

def eraseVar {Φ} {Γ : Ctx Φ} {k} {a : Ty Φ k} : InCtx Γ a → Nat
| .here => 0
| .there x => .succ (eraseVar x)

def erase {Φ Γ a} : Expr Φ Γ a → RawExpr
| .natLit n => .natLit n
| .trueLit => .trueLit
| .falseLit => .falseLit
| .var x => .var (eraseVar x)
| .app e1 e2 => .app (erase e1) (erase e2)
| .lam (a := a) e => .lam (eraseKinds a) (erase e)
| .tyLam k e _ => .tyLam k (erase e)
| .tyApp e b _ => .tyApp (erase e) (eraseKinds b)

inductive TCError : Type where
| mismatch : TCError
| kindError : KindCheckError → TCError
| cannotInfer : TCError

def checkVar {Φ k} (a : Ty Φ k) :
    (Γ : Ctx Φ) →
    Nat →
    Except TCError (InCtx Γ a)
| .empty, _ => .error .mismatch
| .extend Γ b, 0 =>
    match decEq a b with
    | isTrue h => by
        cases h
        exact .ok .here
    | isFalse _ => .error .mismatch
| .extend Γ b, .succ i => do
    let p ← checkVar a Γ i
    .ok (InCtx.there p)

def inferVar {Φ} :
    (Γ : Ctx Φ) →
    Nat →
    Except TCError (Σ k, Σ a : Ty Φ k, InCtx Γ a)
| .empty, _ => .error .cannotInfer
| .extend (k := k) _ b, 0 => .ok (.mk k (.mk b .here))
| .extend Γ _, .succ x => do
    let ⟨k, a, y⟩ ← inferVar Γ x
    .ok (.mk k (.mk a (.there y)))

def tcCheckKinds (Φ : KindCtx) (k : Kind) (a : RawTy)
    : Except TCError (Ty Φ k) :=
  match checkKinds Φ k a with
  | .error e => .error (.kindError e)
  | .ok a' => .ok a'

-- check/infer
mutual
def check {Φ} (Γ : Ctx Φ)
    : (a : Ty Φ .TyKind) → RawExpr → Except TCError (Expr Φ Γ a)
| .NatTy, .natLit n => .ok (.natLit n)
| _, .natLit _ => .error .mismatch

| .BoolTy, .trueLit => .ok .trueLit
| .BoolTy, .falseLit => .ok .falseLit
| _, .trueLit => .error .mismatch
| _, .falseLit => .error .mismatch

| a, .var x => do
    let p ← checkVar a Γ x
    .ok (.var p)

| b0, .app e1 e2 => do
    let ⟨t, e1'⟩ ← infer Γ e1
    match t with
    | .FunTy a b =>
        match decEq b b0 with
        | isFalse _ => .error .mismatch
        | isTrue h => do
            let e2' ← check Γ a e2
            by rw [← h]
               exact .ok (.app e1' e2')

    | _ => .error .mismatch

| .FunTy a b, .lam a'0 e => do
    let a' ← tcCheckKinds Φ .TyKind a'0
    match decEq a a' with
    | isFalse _ => .error .mismatch
    | isTrue _ => do
        let e' ← check (.extend Γ a) b e
        .ok (.lam e')

| _, .lam _ _ => .error .mismatch

| .Forall k a, .tyLam k' e =>
    match decEq k k' with
    | isFalse _ => .error .mismatch
    | isTrue hK => do
        let e' ← check (Φ := Φ.extend k) (renameCtx .there Γ) a e
        .ok (.tyLam k e' rfl)

| _, .tyLam _ _ => .error .mismatch

| a, .tyApp e b => do
    let b' ← tcCheckKinds Φ .TyKind b
    let ⟨t, e'⟩ ← infer Γ e
    match t with
    | .Forall .TyKind a' =>
        match decEq (substTy1 a' b') a with
        | isFalse _ => .error .mismatch
        | isTrue hT => .ok (.tyApp e' b' (.symm hT))
    | _ => .error .mismatch


def infer {Φ} (Γ : Ctx Φ)
    : RawExpr → Except TCError (Σ a, Expr Φ Γ a)
| .natLit n => .ok (.mk .NatTy (.natLit n))
| .trueLit => .ok (.mk .BoolTy .trueLit)
| .falseLit => .ok (.mk .BoolTy .falseLit)
| .var x => do
    let ⟨_k, a, p⟩ ← inferVar Γ x
    .ok (.mk a (.var p))
| .app e1 e2 => do
    let ⟨t, e1'⟩ ← infer Γ e1
    match t with
    | .FunTy a b => do
        let e2' ← check Γ a e2
        .ok (.mk b (.app e1' e2'))
    | _ => .error .mismatch
| .lam a e => do
    let a' ← tcCheckKinds Φ .TyKind a
    let ⟨b, e'⟩ ← infer (Γ.extend a') e
    .ok (.mk (.FunTy a' b) (.lam e'))

| .tyLam k e => do
    let ⟨a', e'⟩ ← @infer (Φ.extend k) (renameCtx .there Γ) e
    .ok (.mk (.Forall k a') (.tyLam k e' (.refl _)))

| .tyApp e b => do
    let ⟨a0, e'⟩ ← infer Γ e
    match a0 with
      | .Forall _k a => do
          let b' ← tcCheckKinds Φ .TyKind b
          .ok (.mk (substTy1 a b') (.tyApp e' b' (.refl _)))

      | _ => .error .mismatch
end
