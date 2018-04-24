--------------------------------------------------------------------------------
-- Hereditary substitutions for weak λ-calculus.                              --
--------------------------------------------------------------------------------

module Calculus where

open import Data.List.Base using (List;[];[_];_∷_;map;mapMaybe;_++_;fromMaybe)
open import Data.Product using (∃; _,_; ,_; proj₂)
import Data.Product as P
open import Data.Maybe using (Maybe;just;nothing)
import Data.Maybe as M
open import Relation.Binary.PropositionalEquality using (_≡_;sym;cong;refl;cong₂)
import Relation.Binary.PropositionalEquality as PE
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)
import Data.List.Properties as P
open import Function using (_∋_;id)
open import Data.Bool
open import Relation.Nullary
open import Relation.Nullary.Decidable using (⌊_⌋)

-- Simple types

data Ty : Set where
  ○ : Ty
  _⇒_ : Ty → Ty → Ty

-- De Bruijn contexts

data Con : Set where
  ε : Con
  _,_ : Con → Ty → Con

-- De Bruijn indices (the set of variables)

data Var : Con → Ty → Set where
  vz : ∀ {Γ a} → Var (Γ , a) a
  vs : ∀ {b Γ a} → Var Γ a → Var (Γ , b) a

-- Removing a variable from a context

_-_ : {a : Ty} → (Γ : Con) → Var Γ a → Con
ε       - ()
(Γ , a) - vz     = Γ
(Γ , b) - (vs x) = (Γ - x) , b

-- Conversely, adding a variable to a context (weakening)

wkv : ∀ {Γ a b} → (x : Var Γ a) → Var (Γ - x) b → Var Γ b
wkv vz     y      = vs y
wkv (vs x) vz     = vz
wkv (vs x) (vs y) = vs (wkv x y)

wkv⁻¹ : ∀ {Γ a b} → (x : Var Γ a) → Var Γ b → Maybe (Var (Γ - x) b)
wkv⁻¹ vz vz         = nothing
wkv⁻¹ vz (vs y)     = just y
wkv⁻¹ (vs x) vz     = just vz
wkv⁻¹ (vs x) (vs y) = M.map vs (wkv⁻¹ x y)

wkv⁻¹-same : ∀ {Γ a} → (v : Var Γ a) → wkv⁻¹ v v ≡ nothing
wkv⁻¹-same vz                          = refl
wkv⁻¹-same (vs v) rewrite wkv⁻¹-same v = refl

wkv-dir1 : ∀ {Γ a b}(x : Var Γ a)(v : Var (Γ - x) b) → wkv⁻¹ x (wkv x v) ≡ just v
wkv-dir1 vz vz         = refl
wkv-dir1 vz (vs v)     = refl
wkv-dir1 (vs x) vz     = refl
wkv-dir1 (vs x) (vs v) = cong (M.map vs) (wkv-dir1 x v)

-- The equality between variables: the predicate...
data EqV {Γ : Con} : {a b : Ty} → Var Γ a → Var Γ b → Set where
  same : ∀{a} → {x : Var Γ a} → EqV {Γ} {a} {a} x x
  diff : ∀{a b} → (x : Var Γ a) → (y : Var (Γ - x) b)
       → EqV {Γ} {a} {b} x (wkv x y)

-- ... and the function that decides it
eq : ∀ {Γ a b} → (x : Var Γ a) → (y : Var Γ b) → EqV x y
eq vz      vz     = same
eq vz      (vs x) = diff vz x
eq (vs x)  vz     = diff (vs x) vz
eq (vs x)  (vs y) with eq x y
eq (vs x)  (vs .x)         | same       = same
eq (vs .x) (vs .(wkv x y)) | (diff x y) = diff (vs x) (vs y)

-- Also, a list of locked variables
■L : Con → Set
■L Γ = List (∃ (Var Γ))

coalesce : ∀{Γ a} (x : Var Γ a) → ■L Γ → ■L (Γ - x)
coalesce v₁ [] = []
coalesce v₁ (v₂ ∷ l) = fromMaybe (M.map ,_ (wkv⁻¹ v₁ (proj₂ v₂))) ++ (coalesce v₁ l)

-- Meditare sul fatto che questo non si puo' scrivere
-- show : ∀{Γ a} → ∃ (Var Γ) → Var Γ a
-- show (_ , v) = {!v!}

-- The set of normal forms
mutual
  data Nf (Ψ Γ : Con) : (l : ■L Γ) (a : Ty) → Set where
    λn : ∀{a b l₁} → Nf Ψ (Γ , a) l₁ b → Nf Ψ Γ (coalesce vz l₁) (a ⇒ b)
    ne : ∀{a b l₁ l₂} → Head Ψ Γ l₁ a → Sp Ψ Γ l₂ a b → Nf Ψ Γ (l₁ ++ l₂) b

  data Head (Ψ Γ : Con) : (l : ■L Γ) (a : Ty) → Set where
    var   : ∀{a} (v : Var Γ a) → Head Ψ Γ [(_ , v)] a
    con   : ∀{a} (c : Var Ψ a) → Head Ψ Γ [] a
    app■  : ∀{a b l₁ l₂} (n₁ : Nf Ψ Γ l₁ (a ⇒ b)) (n₂ : Nf Ψ Γ l₂ a) → Head Ψ Γ (l₁ ++ l₂) b

  data Sp (Ψ Γ : Con) : (l : ■L Γ) → Ty → Ty → Set where
    ε   : ∀ {a} → Sp Ψ Γ [] a a
    _,_ : ∀ {a b c l₁ l₂} → Nf Ψ Γ l₁ b → Sp Ψ Γ l₂ a c → Sp Ψ Γ (l₁ ++ l₂) (b ⇒ a) c

firstVarCoal : ∀{Γ a}(v : Var Γ a)(l : ■L Γ) → coalesce v l ≡ coalesce v ((_ , v) ∷ l)
firstVarCoal v l rewrite wkv⁻¹-same v = refl

-- coalesce is associative
coal-assoc : ∀{Γ a}(v : Var Γ a)(l₁ l₂ l₃ : ■L Γ)
             → coalesce v ((l₁ ++ l₂) ++ l₃) ≡ coalesce v (l₁ ++ l₂ ++ l₃)
coal-assoc v [] l₂ l₃ = refl
coal-assoc v (x ∷ l₁) l₂ l₃ = cong₂ _++_ {fromMaybe (M.map ,_ (wkv⁻¹ v (proj₂ x)))} refl (coal-assoc v l₁ l₂ l₃)

coal-distrib : ∀{Γ a}(v : Var Γ a)(l₁ l₂ : ■L Γ) → coalesce v (l₁ ++ l₂) ≡ coalesce v l₁ ++ coalesce v l₂
coal-distrib v [] l₂       = refl
coal-distrib v (x ∷ l₁) l₂ rewrite P.++-assoc (fromMaybe (M.map ,_ (wkv⁻¹ v (proj₂ x)))) (coalesce v l₁) (coalesce v l₂)
  = cong₂ _++_ {fromMaybe (M.maybe (λ x₁ → just (P.proj₁ x , x₁)) nothing (wkv⁻¹ v (proj₂ x)))} refl (coal-distrib v l₁ l₂)

-- coalesce behaves like a map, with a lemma
coalMap' : ∀{Γ a}(v : Var Γ a)(l₁ l₂ l₃ : ■L Γ) → coalesce v (l₁ ++ l₂ ++ l₃) ≡ coalesce v l₁ ++ coalesce v l₂ ++ coalesce v l₃
coalMap' v [] l₂ l₃ rewrite coal-distrib v l₂ l₃ = refl
coalMap' v (x ∷ l₁) l₂ l₃ rewrite P.++-assoc (fromMaybe (M.map ,_ (wkv⁻¹ v (proj₂ x)))) (coalesce v l₁) (coalesce v l₂ ++ coalesce v l₃)
  = cong₂ _++_ {fromMaybe (M.maybe (λ x₁ → just (P.proj₁ x , x₁)) nothing (wkv⁻¹ v (proj₂ x)))} refl (coalMap' v l₁ l₂ l₃)

coalMap : ∀{Γ a}(v : Var Γ a)(l₁ l₂ l₃ : ■L Γ)
        → coalesce v ((l₁ ++ l₂) ++ l₃) ≡ (coalesce v l₁ ++ coalesce v l₂) ++ coalesce v l₃
coalMap v l₁ l₂ l₃ rewrite coal-assoc v l₁ l₂ l₃ | P.++-assoc (coalesce v l₁) (coalesce v l₂) (coalesce v l₃) | coalMap' v l₁ l₂ l₃
  = refl

coal-aux : ∀{Γ a b}(v : Var Γ a)(l : ■L (Γ , b)) → coalesce {a = a} v (coalesce {a = b} vz l) ≡ coalesce {a = b} vz (coalesce {a = a} (vs v) l)
coal-aux v [] = refl
coal-aux v ((_ , vz) ∷ l) = coal-aux v l
coal-aux v ((_ , vs x) ∷ l) with eq v x
coal-aux v ((_ , vs .v) ∷ l) | same rewrite wkv⁻¹-same v = coal-aux v l
coal-aux v ((a , vs .(wkv v y)) ∷ l) | diff .v y rewrite wkv-dir1 v y = cong₂ _∷_ {(a , y)} refl (coal-aux v l)

wk∃v :  ∀{Γ a} (x : Var Γ a) → ∃ (Var (Γ - x)) → ∃ (Var Γ)
wk∃v x (a , v) = (a , wkv x v)

wk■L : ∀{Γ a} (x : Var Γ a) → ■L (Γ - x) → ■L Γ
wk■L v l = map (wk∃v v) l

wk■L-lemma : ∀{Γ a b}(v : Var Γ a)(l : ■L (Γ - v , b)) → wk■L v (coalesce vz l) ≡ coalesce vz (wk■L (vs v) l)
wk■L-lemma v [] = refl
wk■L-lemma vz ((_ , vz) ∷ l)       = wk■L-lemma vz l
wk■L-lemma vz ((_ , vs x) ∷ l)     = cong₂ _∷_ {_ , vs x} refl (wk■L-lemma vz l)
wk■L-lemma (vs v) ((_ , vz) ∷ l)   = wk■L-lemma (vs v) l
wk■L-lemma (vs v) ((_ , vs x) ∷ l) = cong₂ _∷_ {_ , wkv (vs v) x} refl (wk■L-lemma (vs v) l)

manual : ∀ {a b Γ} (x : Var Γ a) (l₁ : List (∃ (Var ((Γ - x) , b)))) → wk■L x (coalesce vz l₁) ≡ coalesce vz (wk■L (vs x) l₁)
manual v [] = refl
manual v ((c , vz) ∷ l)   = manual v l
manual v ((c , vs x) ∷ l) = cong₂ _∷_ {c , wkv v x} refl (manual v l)

-- Weakening of normal forms
mutual
  wkNf : ∀ {Ψ Γ a b}(x : Var Γ a){l : ■L (Γ - x)} → Nf Ψ (Γ - x) l b → Nf Ψ Γ (wk■L x l) b
  wkNf x (λn {l₁ = l₁} n) rewrite manual x l₁ = λn (wkNf (vs x) n)
  wkNf {Γ = Γ} x (ne {l₁ = l₁}{l₂ = l₂} h S)
    rewrite P.map-++-commute (wk∃v x) l₁ l₂
    = ne (wkHd x h) (wkSp x S)

  wkHd : ∀ {Ψ Γ a b} → (x : Var Γ a){l : ■L (Γ - x)} → Head Ψ (Γ - x) l b → Head Ψ Γ (wk■L x l) b
  wkHd {Ψ = Ψ} x (var v) = var {Ψ = Ψ} (wkv x v)
  wkHd {Γ = Γ} x (con c) = con {Γ = Γ} c
  wkHd {Γ = Γ} x (app■ {l₁ = l₁} {l₂ = l₂} n₁ n₂)
    rewrite P.map-++-commute (wk∃v x) l₁ l₂
    = app■ (wkNf x n₁) (wkNf x n₂)

  wkSp :  ∀ {Ψ Γ a b c} → (v : Var Γ a){l : ■L (Γ - v)} → Sp Ψ (Γ - v) l b c → Sp Ψ Γ (wk■L v l) b c
  wkSp v ε = ε
  wkSp v (_,_ {l₁ = l₁} {l₂ = l₂} n S) rewrite ((P.map-++-commute (wk∃v v) l₁ l₂)) = wkNf v n , wkSp v S

-- Add a normal form at the end of a spine
appSp : ∀ {Ψ Γ l₁ l₂ a b c} → Sp Ψ Γ l₁ c (a ⇒ b) → Nf Ψ Γ l₂ a → Sp Ψ Γ (l₁ ++ l₂) c b
appSp {l₂ = l₂} {b = b} ε u                    = PE.subst (λ t → Sp _ _ t _ _) (P.++-identityʳ l₂)         (u , ε)
appSp {l₂ = l₃} (_,_ {l₁ = l₁}{l₂ = l₂} n S) u = PE.subst (λ t → Sp _ _ t _ _) (sym (P.++-assoc l₁ l₂ l₃)) (n , appSp S u)

nvar : ∀ {Ψ Γ a} → (v : Var Γ a) → Nf Ψ Γ [ (_ , v) ] a
nvar x = ne (var x) ε

ncon : ∀ {Ψ Γ a} → Var Ψ a → Nf Ψ Γ [] a
ncon x = ne (con x) ε

-- Hereditary substitutions: substitute a variable by a normal form and
-- normalize the result

-- Predicate that controls that every element in a list is vz
all-vz : ∀{Γ}(l : ■L Γ) → Bool
all-vz []               = true
all-vz ((_ , vz)   ∷ l) = all-vz l
all-vz ((_ , vs v) ∷ l) = false

-- Get ■L from a normal form
get■L : ∀{Ψ Γ l a} → Nf Ψ Γ l a → ■L Γ
get■L {l = l} _ = l

isEmpty : ∀{a : Set} → List a → Bool
isEmpty []      = true
isEmpty (_ ∷ _) = false

isEmpty' : ∀{a : Set} → (l : List a) → Dec (l ≡ [])
isEmpty' []      = yes refl
isEmpty' (_ ∷ _) = no (λ ())

aux : ∀ {a Γ a₁} (v : Var Γ a₁) (l : ■L (Γ , a)) → coalesce vz (coalesce (vs v) l) ≡ coalesce v (coalesce vz l)
aux v []               = refl
aux v ((_ , vz)   ∷ l) = aux v l
aux v ((_ , vs x) ∷ l) with eq v x
aux v ((_ , vs .v) ∷ l) | same rewrite wkv⁻¹-same v = aux v l
aux v ((a , vs .(wkv v y)) ∷ l) | diff .v y rewrite wkv-dir1 v y = cong₂ _∷_ {(a , y)} refl (aux v l)

{-# TERMINATING #-}
mutual
  napp : ∀ {Ψ Γ l₁ l₂ b a} → Nf Ψ Γ l₁ (a ⇒ b) → Nf Ψ Γ l₂ a → Nf Ψ Γ (l₁ ++ l₂) b
  napp {l₁ = l₁} {l₂ = l₂} n₁ n₂ with isEmpty' l₁ | isEmpty' l₂
  napp {l₁ = l₁} {.[]} (λn {l₁ = li₁} n₁)              n₂   | yes p | yes refl =
    PE.subst (λ l → Nf _ _ l _) (sym (P.++-identityʳ (coalesce vz li₁))) (n₁ [ vz := n₂ ])
  napp {l₁ = l₁} {.[]} (ne {l₁ = li₁} {l₂ = li₂} x sp) n₂ | yes p | yes refl =
    PE.subst (λ l → Nf _ _ l _) (sym (P.++-assoc li₁ li₂ [])) (ne x (appSp sp n₂))
  napp {l₁ = l₁} {l₂} n₁ n₂ | yes p | no ¬p =
    PE.subst (λ l → Nf _ _ l _) (P.++-identityʳ (l₁ ++ l₂)) (ne (app■ n₁ n₂) ε)
  napp {l₁ = l₁} {l₂} n₁ n₂ | no ¬p | b =
    PE.subst (λ l → Nf _ _ l _) (P.++-identityʳ (l₁ ++ l₂)) (ne (app■ n₁ n₂) ε)

  _[_:=_] : ∀ {Ψ Γ l₁ a b}
          → (Nf Ψ Γ l₁ b) → (x : Var Γ a) → Nf Ψ (Γ - x) [] a → Nf Ψ (Γ - x) (coalesce x l₁) b
  _[_:=_] (λn {l₁ = l₁} n) x u = PE.subst (λ t → Nf _ _ t _) (aux x l₁) (λn (n [ vs x := wkNf vz u ]))
  ne (var v) sp [ x := u ] with eq x v
  ne (var v) sp [ .v := u ]         | same rewrite (wkv⁻¹-same v) = u ◇ (sp < v := u >)
  ne (var .(wkv x y)) sp [ x := u ] | diff .x y rewrite (wkv-dir1 x y) = ne (var y) (sp < x := u >)
  ne (con c) sp [ x := u ] = ne (con c) (sp < x := u >)
  ne {l₂ = l₃} (app■ {l₁ = l₁} {l₂} n₁ n₂) sp [ x := u ] =
    PE.subst (λ l → Nf _ _ l _)
             (sym (begin
             coalesce x ((l₁ ++ l₂) ++ l₃) ≡⟨ coal-distrib x (l₁ ++ l₂) l₃ ⟩
             coalesce x (l₁ ++ l₂) ++ coalesce x l₃ ≡⟨ PE.cong (λ t → t ++ coalesce x l₃) (coal-distrib x l₁ l₂) ⟩
             (coalesce x l₁ ++ coalesce x l₂) ++ coalesce x l₃ ≡⟨ P.++-assoc (coalesce x l₁) _ _ ⟩
             coalesce x l₁ ++ coalesce x l₂ ++ coalesce x l₃
             ∎
             ))
             ((n₁ [ x := u ]) ◇ (n₂ [ x := u ] , sp < x := u >))

  _<_:=_> : ∀ {Ψ Γ l₁ a b c}
          → (Sp Ψ Γ l₁ b c) → (x : Var Γ a) → Nf Ψ (Γ - x) [] a
          → Sp Ψ (Γ - x) (coalesce x l₁) b c
  ε < x := u > = ε
  (_,_ {l₁ = l₁} {l₂} n sp) < x := u > = PE.subst (λ l → Sp _ _ l _ _) (sym (coal-distrib x l₁ l₂)) (n [ x := u ] , sp < x := u >)

  -- apply a normal form to a spine
  _◇_ : ∀ {Ψ Γ a b l₁ l₂} → Nf Ψ Γ l₁ a → Sp Ψ Γ l₂ a b → Nf Ψ Γ (l₁ ++ l₂) b
  n ◇ ε        = PE.subst (λ l → Nf _ _ l _) (sym (P.++-identityʳ _)) n
  _◇_ {l₁ = l₁} n₁ (_,_ {l₁ = l₂} {l₂ = l₃} n₂ sp) = PE.subst (λ l → Nf _ _ l _) (P.++-assoc l₁ l₂ l₃) ((napp n₁ n₂) ◇ sp)

-- The set of terms
data Tm (Ψ Γ : Con) : (a : Ty) → Set where
  var : ∀ {a} → Var Γ a → Tm Ψ Γ a
  con : ∀ {a} → Var Ψ a → Tm Ψ Γ a
  Λ   : ∀ {a b} → Tm Ψ (Γ , a) b → Tm Ψ Γ (a ⇒ b)
  app : ∀ {a b} → Tm Ψ Γ (a ⇒ b) → Tm Ψ Γ a → Tm Ψ Γ b

annotateTerm : ∀{Ψ Γ a} → Tm Ψ Γ a → ■L Γ
annotateTerm (var x) = [ (_ , x) ]
annotateTerm (con x) = []
annotateTerm (Λ t) = coalesce vz (annotateTerm t)
annotateTerm (app t₁ t₂) = annotateTerm t₁ ++ annotateTerm t₂

-- The terms normalizer
nf : ∀ {Ψ Γ a} → (t : Tm Ψ Γ a) → Nf Ψ Γ (annotateTerm t) a
nf (var x)   = nvar x
nf (con x)   = ncon x
nf (Λ t)     = λn (nf t)
nf (app t u) = napp (nf t) (nf u)

-- -- nf (Λ (Λ (app (var (vs vz)) (var vz))))

-- Embedding normal forms into terms Normal forms are not defined as a subset of
-- terms, but can be seen as such:
mutual
  -- Embedding of normal forms
  ⌈_⌉ : ∀ {Ψ Γ a l} → Nf Ψ Γ l a → Tm Ψ Γ a
  ⌈ λn x ⌉ = Λ ⌈ x ⌉
  ⌈ ne (var v) S ⌉ = embSp S (var v)
  ⌈ ne (con c) S ⌉ = embSp S (con c)
  ⌈ ne (app■ n₁ n₂) S ⌉ = embSp S (app ⌈ n₁ ⌉ ⌈ n₂ ⌉ )

--   -- Embedding of sp
--   -- We have to use an accumulator
  embSp : ∀ {Ψ Γ a b l} → Sp Ψ Γ l a b → Tm Ψ Γ a → Tm Ψ Γ b
  embSp ε acc = acc
  embSp (n , S) acc = embSp S (app acc ⌈ n ⌉ )

-- Weakening a term
wkTm : ∀ {Ψ a Γ b} → (x : Var Γ a) → Tm Ψ (Γ - x) b → Tm Ψ Γ b
wkTm x (var v) = var (wkv x v)
wkTm x (con v) = con v
wkTm x (Λ t) = Λ (wkTm (vs x) t)
wkTm x (app t₁ t₂) = app (wkTm x t₁) (wkTm x t₂)

-- Substitutions hide variables and terms
substVar : ∀ {Ψ a Γ b}
         → Var Γ b → (x : Var Γ a) → Tm Ψ (Γ - x) a
         → Tm Ψ (Γ - x) b
substVar v x u with eq x v
substVar v .v u | same = u
substVar .(wkv v x) .v u | diff v x = var x

subst : ∀ {Ψ a Γ b}
      → Tm Ψ Γ b → (x : Var Γ a) → Tm Ψ (Γ - x) a
      → Tm Ψ (Γ - x) b
subst (var v) x u = substVar v x u
subst (con v) x u = con v
subst (Λ t) x u = Λ (subst t (vs x) (wkTm vz u))
subst (app t₁ t₂) x u = app (subst t₁ x u) (subst t₂ x u)

-- module Examples where
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
