--------------------------------------------------------------------------------
-- Hereditary substitutions for weak λ-calculus.
--------------------------------------------------------------------------------
module Calculus where

open import Data.List.Base
  using (List;[];[_];_∷_;map;_++_;fromMaybe)
open import Data.List.Properties
  using (++-assoc;++-identityʳ;map-++-commute)
open import Data.Maybe
  using (Maybe;just;nothing;maybe) renaming (map to mapMaybe)
open import Data.Product
  using (∃; _,_; ,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_;refl;sym;cong;cong₂;subst;module ≡-Reasoning)
open import Relation.Nullary
  using (Dec;yes;no)
open import Relation.Nullary.Decidable
  using (⌊_⌋)

--------------------------------------------------------------------------------
-- Types, Contexts and Variables
--------------------------------------------------------------------------------
data Ty : Set where
  ○ : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ε : Con
  _,_ : Con → Ty → Con

data Var : Con → Ty → Set where
  vz : ∀ {Γ a}             → Var (Γ , a) a
  vs : ∀ {b Γ a} → Var Γ a → Var (Γ , b) a

--------------------------------------------------------------------------------
-- Weakening for variables (and partial inverses)
--------------------------------------------------------------------------------
_-_ : {a : Ty} → (Γ : Con) → Var Γ a → Con
ε       - ()
(Γ , a) - vz     = Γ
(Γ , b) - (vs x) = (Γ - x) , b

wkv : ∀ {Γ a b} → (x : Var Γ a) → Var (Γ - x) b → Var Γ b
wkv vz     y      = vs y
wkv (vs x) vz     = vz
wkv (vs x) (vs y) = vs (wkv x y)

wkv⁻¹ : ∀{Γ a b} (x : Var Γ a) → Var Γ b
      → Maybe (Var (Γ - x) b)
wkv⁻¹ vz vz         = nothing
wkv⁻¹ vz (vs y)     = just y
wkv⁻¹ (vs x) vz     = just vz
wkv⁻¹ (vs x) (vs y) = mapMaybe vs (wkv⁻¹ x y)

wkv⁻¹-same : ∀ {Γ a} (v : Var Γ a)
           → wkv⁻¹ v v ≡ nothing
wkv⁻¹-same vz                          = refl
wkv⁻¹-same (vs v) rewrite wkv⁻¹-same v = refl

wkv⁻¹∘wkv : ∀ {Γ a b}(x : Var Γ a)(v : Var (Γ - x) b)
          → wkv⁻¹ x (wkv x v) ≡ just v
wkv⁻¹∘wkv vz vz         = refl
wkv⁻¹∘wkv vz (vs v)     = refl
wkv⁻¹∘wkv (vs x) vz     = refl
wkv⁻¹∘wkv (vs x) (vs v) = cong (mapMaybe vs) (wkv⁻¹∘wkv x v)

--------------------------------------------------------------------------------
-- Equality between variables
--------------------------------------------------------------------------------
data EqV {Γ : Con} : {a b : Ty} → Var Γ a → Var Γ b → Set where
  same : ∀{a} → {x : Var Γ a} → EqV {Γ} {a} {a} x x
  diff : ∀{a b} → (x : Var Γ a) → (y : Var (Γ - x) b)
       → EqV {Γ} {a} {b} x (wkv x y)

eq : ∀ {Γ a b} → (x : Var Γ a) → (y : Var Γ b) → EqV x y
eq vz      vz     = same
eq vz      (vs x) = diff vz x
eq (vs x)  vz     = diff (vs x) vz
eq (vs x)  (vs y) with eq x y
eq (vs x)  (vs .x)         | same       = same
eq (vs .x) (vs .(wkv x y)) | (diff x y) = diff (vs x) (vs y)

--------------------------------------------------------------------------------
-- Existential lists, remotion from an existential list and properties
--------------------------------------------------------------------------------
■L : Con → Set
■L Γ = List (∃ (Var Γ))

empty? : ∀{a : Set} → (l : List a) → Dec (l ≡ [])
empty? []      = yes refl
empty? (_ ∷ _) = no (λ ())

_⊟_ : ∀{Γ a} → ■L Γ → (x : Var Γ a) → ■L (Γ - x)
_⊟_ []       v₁  =  []
_⊟_ (v₂ ∷ l) v₁  =  fromMaybe (mapMaybe ,_ (wkv⁻¹ v₁ (proj₂ v₂))) ++ (l ⊟ v₁)

⊟-assoc : ∀{Γ a}(v : Var Γ a)(l₁ l₂ l₃ : ■L Γ)
        → ((l₁ ++ l₂) ++ l₃) ⊟ v  ≡ (l₁ ++ l₂ ++ l₃) ⊟ v
⊟-assoc v [] l₂ l₃ = refl
⊟-assoc v (x ∷ l₁) l₂ l₃ = cong₂ _++_ {fromMaybe (mapMaybe ,_ (wkv⁻¹ v (proj₂ x)))} refl (⊟-assoc v l₁ l₂ l₃)

⊟-distrib : ∀{Γ a}(v : Var Γ a)(l₁ l₂ : ■L Γ)
          → (l₁ ++ l₂) ⊟ v ≡ l₁ ⊟ v ++ l₂ ⊟ v
⊟-distrib v [] l₂       = refl
⊟-distrib v (x ∷ l₁) l₂ rewrite ++-assoc (fromMaybe (mapMaybe ,_ (wkv⁻¹ v (proj₂ x)))) (l₁ ⊟ v) (l₂ ⊟ v)
  = cong₂ _++_ {fromMaybe (maybe (λ x₁ → just (proj₁ x , x₁)) nothing (wkv⁻¹ v (proj₂ x)))} refl (⊟-distrib v l₁ l₂)

⊟/⊟ : ∀{a Γ a₁}(v : Var Γ a₁)(l : ■L (Γ , a))
    → (l ⊟ vs v) ⊟ vz  ≡  (l ⊟ vz) ⊟ v
⊟/⊟ v []               = refl
⊟/⊟ v ((_ , vz)   ∷ l) = ⊟/⊟ v l
⊟/⊟ v ((_ , vs x) ∷ l) with eq v x
⊟/⊟ v ((_ , vs .v) ∷ l) | same rewrite wkv⁻¹-same v = ⊟/⊟ v l
⊟/⊟ v ((a , vs .(wkv v y)) ∷ l) | diff .v y rewrite wkv⁻¹∘wkv v y = cong₂ _∷_ {(a , y)} refl (⊟/⊟ v l)

--------------------------------------------------------------------------------
-- The set of normal forms
--------------------------------------------------------------------------------
mutual
  data Nf (Ψ Γ : Con) : (l : ■L Γ) (a : Ty) → Set where
    λn : ∀{a b l₁} → Nf Ψ (Γ , a) l₁ b → Nf Ψ Γ (l₁ ⊟ vz) (a ⇒ b)
    ne : ∀{a b l₁ l₂} → Head Ψ Γ l₁ a → Sp Ψ Γ l₂ a b → Nf Ψ Γ (l₁ ++ l₂) b

  data Head (Ψ Γ : Con) : (l : ■L Γ) (a : Ty) → Set where
    var   : ∀{a} (v : Var Γ a) → Head Ψ Γ [(_ , v)] a
    con   : ∀{a} (c : Var Ψ a) → Head Ψ Γ [] a
    app■  : ∀{a b l₁ l₂}(n₁ : Nf Ψ Γ l₁ (a ⇒ b))(n₂ : Nf Ψ Γ l₂ a) → Head Ψ Γ (l₁ ++ l₂) b

  data Sp (Ψ Γ : Con) : (l : ■L Γ) → Ty → Ty → Set where
    ε   : ∀ {a} → Sp Ψ Γ [] a a
    _,_ : ∀ {a b c l₁ l₂} → Nf Ψ Γ l₁ b → Sp Ψ Γ l₂ a c → Sp Ψ Γ (l₁ ++ l₂) (b ⇒ a) c

--------------------------------------------------------------------------------
-- Weakening for existential variables, list, and normal forms
--------------------------------------------------------------------------------
wk∃v :  ∀{Γ a} (x : Var Γ a) → ∃ (Var (Γ - x)) → ∃ (Var Γ)
wk∃v x (a , v) = (a , wkv x v)

wk■L : ∀{Γ a} (x : Var Γ a) → ■L (Γ - x) → ■L Γ
wk■L v l = map (wk∃v v) l

wk■L/⊟ : ∀{a b Γ}(x : Var Γ a)(l₁ : ■L ((Γ - x) , b))
       → wk■L x (l₁ ⊟ vz) ≡ (wk■L (vs x) l₁) ⊟ vz
wk■L/⊟ v [] = refl
wk■L/⊟ v ((c , vz) ∷ l)   = wk■L/⊟ v l
wk■L/⊟ v ((c , vs x) ∷ l) = cong₂ _∷_ {c , wkv v x} refl (wk■L/⊟ v l)

mutual
  wkNf : ∀{Ψ Γ a b}(x : Var Γ a){l : ■L (Γ - x)}
       → Nf Ψ (Γ - x) l b → Nf Ψ Γ (wk■L x l) b
  wkNf x (λn {l₁ = l₁} n) rewrite wk■L/⊟ x l₁ = λn (wkNf (vs x) n)
  wkNf {Γ = Γ} x (ne {l₁ = l₁}{l₂ = l₂} h S)
    rewrite map-++-commute (wk∃v x) l₁ l₂
    = ne (wkHd x h) (wkSp x S)

  wkHd : ∀{Ψ Γ a b}(x : Var Γ a){l : ■L (Γ - x)}
       → Head Ψ (Γ - x) l b → Head Ψ Γ (wk■L x l) b
  wkHd {Ψ = Ψ} x (var v) = var {Ψ = Ψ} (wkv x v)
  wkHd {Γ = Γ} x (con c) = con {Γ = Γ} c
  wkHd {Γ = Γ} x (app■ {l₁ = l₁} {l₂ = l₂} n₁ n₂)
    rewrite map-++-commute (wk∃v x) l₁ l₂
    = app■ (wkNf x n₁) (wkNf x n₂)

  wkSp :  ∀{Ψ Γ a b c}(v : Var Γ a){l : ■L (Γ - v)}
       → Sp Ψ (Γ - v) l b c → Sp Ψ Γ (wk■L v l) b c
  wkSp v ε = ε
  wkSp v (_,_ {l₁ = l₁} {l₂ = l₂} n S) rewrite ((map-++-commute (wk∃v v) l₁ l₂)) = wkNf v n , wkSp v S

--------------------------------------------------------------------------------
-- Interpretation functions
--------------------------------------------------------------------------------
appSp : ∀ {Ψ Γ l₁ l₂ a b c} → Sp Ψ Γ l₁ c (a ⇒ b) → Nf Ψ Γ l₂ a → Sp Ψ Γ (l₁ ++ l₂) c b
appSp {l₂ = l₂} {b = b} ε u                    = subst (λ t → Sp _ _ t _ _) (++-identityʳ l₂)         (u , ε)
appSp {l₂ = l₃} (_,_ {l₁ = l₁}{l₂ = l₂} n S) u = subst (λ t → Sp _ _ t _ _) (sym (++-assoc l₁ l₂ l₃)) (n , appSp S u)

nvar : ∀ {Ψ Γ a} → (v : Var Γ a) → Nf Ψ Γ [ (_ , v) ] a
nvar x = ne (var x) ε

ncon : ∀ {Ψ Γ a} → Var Ψ a → Nf Ψ Γ [] a
ncon x = ne (con x) ε

{-# TERMINATING #-}
mutual
  napp : ∀ {Ψ Γ l₁ l₂ b a} → Nf Ψ Γ l₁ (a ⇒ b) → Nf Ψ Γ l₂ a → Nf Ψ Γ (l₁ ++ l₂) b
  napp {l₁ = l₁} {l₂ = l₂} n₁ n₂ with empty? l₁ | empty? l₂
  napp {l₁ = l₁} {.[]} (λn {l₁ = li₁} n₁)              n₂   | yes p | yes refl =
    subst (λ l → Nf _ _ l _) (sym (++-identityʳ (li₁ ⊟ vz))) (n₁ [ vz := n₂ ])
  napp {l₁ = l₁} {.[]} (ne {l₁ = li₁} {l₂ = li₂} x sp) n₂ | yes p | yes refl =
    subst (λ l → Nf _ _ l _) (sym (++-assoc li₁ li₂ [])) (ne x (appSp sp n₂))
  napp {l₁ = l₁} {l₂} n₁ n₂ | yes p | no ¬p =
    subst (λ l → Nf _ _ l _) (++-identityʳ (l₁ ++ l₂)) (ne (app■ n₁ n₂) ε)
  napp {l₁ = l₁} {l₂} n₁ n₂ | no ¬p | b =
    subst (λ l → Nf _ _ l _) (++-identityʳ (l₁ ++ l₂)) (ne (app■ n₁ n₂) ε)

  _[_:=_] : ∀ {Ψ Γ l₁ a b}
    → (Nf Ψ Γ l₁ b) → (x : Var Γ a) → Nf Ψ (Γ - x) [] a → Nf Ψ (Γ - x) (l₁ ⊟ x) b
  _[_:=_] (λn {l₁ = l₁} n) x u = subst (λ t → Nf _ _ t _) (⊟/⊟ x l₁) (λn (n [ vs x := wkNf vz u ]))
  ne (var v) sp [ x := u ] with eq x v
  ne (var v) sp [ .v := u ]         | same rewrite (wkv⁻¹-same v) = u ◇ (sp < v := u >)
  ne (var .(wkv x y)) sp [ x := u ] | diff .x y rewrite (wkv⁻¹∘wkv x y) = ne (var y) (sp < x := u >)
  ne (con c) sp [ x := u ] = ne (con c) (sp < x := u >)
  ne {l₂ = l₃} (app■ {l₁ = l₁} {l₂} n₁ n₂) sp [ x := u ] =
    subst (λ l → Nf _ _ l _)
             (sym (begin
             ((l₁ ++ l₂) ++ l₃) ⊟ x  ≡⟨ ⊟-distrib x (l₁ ++ l₂) l₃ ⟩
             (l₁ ++ l₂) ⊟ x  ++ l₃ ⊟ x ≡⟨ cong (λ t → t ++ l₃ ⊟ x) (⊟-distrib x l₁ l₂) ⟩
             (l₁ ⊟ x ++  l₂ ⊟ x) ++ l₃ ⊟ x  ≡⟨ ++-assoc ( l₁ ⊟ x) _ _ ⟩
             l₁ ⊟ x ++ l₂ ⊟ x ++ l₃ ⊟ x
             ∎
             ))
             ((n₁ [ x := u ]) ◇ (n₂ [ x := u ] , sp < x := u >))
     where open ≡-Reasoning

  _<_:=_> : ∀ {Ψ Γ l₁ a b c}
          → (Sp Ψ Γ l₁ b c) → (x : Var Γ a) → Nf Ψ (Γ - x) [] a
          → Sp Ψ (Γ - x) (l₁ ⊟ x) b c
  ε < x := u > = ε
  (_,_ {l₁ = l₁} {l₂} n sp) < x := u > = subst (λ l → Sp _ _ l _ _) (sym (⊟-distrib x l₁ l₂)) (n [ x := u ] , sp < x := u >)

  _◇_ : ∀ {Ψ Γ a b l₁ l₂} → Nf Ψ Γ l₁ a → Sp Ψ Γ l₂ a b → Nf Ψ Γ (l₁ ++ l₂) b
  n ◇ ε        = subst (λ l → Nf _ _ l _) (sym (++-identityʳ _)) n
  _◇_ {l₁ = l₁} n₁ (_,_ {l₁ = l₂} {l₂ = l₃} n₂ sp) = subst (λ l → Nf _ _ l _) (++-assoc l₁ l₂ l₃) ((napp n₁ n₂) ◇ sp)

--------------------------------------------------------------------------------
-- Terms and normalizer
--------------------------------------------------------------------------------
data Tm (Ψ Γ : Con) : (a : Ty) → Set where
  var : ∀ {a} → Var Γ a → Tm Ψ Γ a
  con : ∀ {a} → Var Ψ a → Tm Ψ Γ a
  Λ   : ∀ {a b} → Tm Ψ (Γ , a) b → Tm Ψ Γ (a ⇒ b)
  app : ∀ {a b} → Tm Ψ Γ (a ⇒ b) → Tm Ψ Γ a → Tm Ψ Γ b

annotate : ∀{Ψ Γ a} → Tm Ψ Γ a → ■L Γ
annotate (var x)     = [ (_ , x) ]
annotate (con x)     = []
annotate (Λ t)       = (annotate t) ⊟ vz
annotate (app t₁ t₂) = annotate t₁ ++ annotate t₂

nf : ∀ {Ψ Γ a} → (t : Tm Ψ Γ a) → Nf Ψ Γ (annotate t) a
nf (var x)   = nvar x
nf (con x)   = ncon x
nf (Λ t)     = λn (nf t)
nf (app t u) = napp (nf t) (nf u)

--------------------------------------------------------------------------------
-- Embeddings
--------------------------------------------------------------------------------
mutual
  ⌈_⌉ : ∀ {Ψ Γ a l} → Nf Ψ Γ l a → Tm Ψ Γ a
  ⌈ λn x ⌉ = Λ ⌈ x ⌉
  ⌈ ne (var v) S ⌉ = embSp S (var v)
  ⌈ ne (con c) S ⌉ = embSp S (con c)
  ⌈ ne (app■ n₁ n₂) S ⌉ = embSp S (app ⌈ n₁ ⌉ ⌈ n₂ ⌉ )

  embSp : ∀ {Ψ Γ a b l} → Sp Ψ Γ l a b → Tm Ψ Γ a → Tm Ψ Γ b
  embSp ε acc = acc
  embSp (n , S) acc = embSp S (app acc ⌈ n ⌉ )

--------------------------------------------------------------------------------
-- Weakening and substitutions for terms
--------------------------------------------------------------------------------
wkTm : ∀ {Ψ a Γ b} → (x : Var Γ a) → Tm Ψ (Γ - x) b → Tm Ψ Γ b
wkTm x (var v) = var (wkv x v)
wkTm x (con v) = con v
wkTm x (Λ t) = Λ (wkTm (vs x) t)
wkTm x (app t₁ t₂) = app (wkTm x t₁) (wkTm x t₂)

substVar : ∀ {Ψ a Γ b}
         → Var Γ b → (x : Var Γ a) → Tm Ψ (Γ - x) a
         → Tm Ψ (Γ - x) b
substVar v x u with eq x v
substVar v .v u | same = u
substVar .(wkv v x) .v u | diff v x = var x

substTm : ∀ {Ψ a Γ b}
      → Tm Ψ Γ b → (x : Var Γ a) → Tm Ψ (Γ - x) a
      → Tm Ψ (Γ - x) b
substTm (var v) x u = substVar v x u
substTm (con v) x u = con v
substTm (Λ t) x u = Λ (substTm t (vs x) (wkTm vz u))
substTm (app t₁ t₂) x u = app (substTm t₁ x u) (substTm t₂ x u)

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------
-- Ovvero (λx.x)z
ex1 : Tm (ε , ○) ε ○
ex1 = app (Λ (var vz)) (con vz)

-- Ovvero λx.(λy.x)z
ex2 : Tm (ε , ○) ε (○ ⇒ ○)
ex2 = Λ (app (Λ (var (vs vz))) (con vz))

-- Ovvero (λx.(λy.xy))z
ex3 : Tm (ε , ○ ⇒ ○) ε (○ ⇒ ○)
ex3 = app (Λ (Λ (app (var (vs vz)) (var vz)))) (con vz)

-- Come ex₂, ma l'applicazione e' al livello superiore
-- quindi (λx.(λy.x))z
ex4 : Tm (ε , ○) ε (○ ⇒ ○)
ex4 = app (Λ (Λ (var (vs vz)))) (con vz)
-- Test per vedere se il caso con in hsubst funziona
-- quindi (λx.(λy.z))w
ex5 : Tm ((ε , ○) , ○) ε (○ ⇒ ○)
ex5 = app (Λ (Λ (con vz))) (con (vs vz))
-- Test per vedere se si possono sbloccare gli elementi interni che erano
-- bloccati.
-- quindi λx.(λy.(λw.w)y)z
ex6 : Tm (ε , ○) ε (○ ⇒ ○)
ex6 = Λ (app (Λ (app (Λ (var vz)) (var vz))) (con vz))

roundtrip : ∀{Ψ Γ a} → Tm Ψ Γ a → Tm Ψ Γ a
roundtrip ex = ⌈ nf ex ⌉
