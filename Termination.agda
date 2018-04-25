module Termination where

open import Calculus
open import Delay

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

napp⇓ : ∀ {Ψ Γ l₁ l₂ b a}(n₁ : Nf Ψ Γ l₁ (a ⇒ b))(n₂ : Nf Ψ Γ l₂ a)
      → napp n₁ n₂ ⇓
napp⇓ {l₁ = l₁} {l₂}  n₁ n₂ with empty? l₁ | empty? l₂
napp⇓ {l₁ = l₁} {.[]} (λn n₁) n₂   | yes p | yes refl = {!!}
napp⇓ {l₁ = l₁} {.[]} (ne {l₁ = li₁} {li₂} x sp) n₂ | yes p | yes refl =
  ((ne x (appSp sp n₂)) fixing■L-Nf (sym (++-assoc li₁ li₂ []))) , now⇓
napp⇓ {l₁ = l₁} {l₂} n₁ n₂  | yes p | no ¬p =
  (ne (app■ n₁ n₂) ε fixing■L-Nf (++-identityʳ (l₁ ++ l₂))) , now⇓
napp⇓ {l₁ = l₁} {l₂} n₁ n₂  | no ¬p | b     =
  (ne (app■ n₁ n₂) ε fixing■L-Nf (++-identityʳ (l₁ ++ l₂))) , now⇓


_[_:=_]⇓ : ∀ {Ψ Γ l₁ a b}
         → (n : Nf Ψ Γ l₁ b) → (x : Var Γ a) → (u : Nf Ψ (Γ - x) [] a)
         → later (n [ x := u ]) ⇓
λn {l₁ = l₁} n [ x := u ]⇓ = let n! , n!⇓ = n [ vs x := wkNf vz u ]⇓
                             in (λn n! fixing■L-Nf ⊟/⊟ x l₁) , {!!}
ne x₁ x₂ [ x := u ]⇓ = {!!}


-- It's difficult to complete that last case without a lemma
normalize : ∀{Ψ Γ a} → (t : Tm Ψ Γ a) → nf t ⇓
normalize (var x) = ne (var x) ε , now⇓
normalize (con x) = ne (con x) ε , now⇓
normalize (Λ t) = let t! , t!⇓ = normalize t
                  in (λn t!) , map⇓ λn t!⇓
normalize (app t₁ t₂) = let t₁! , t₁!⇓ = normalize t₁
                            t₂! , t₂!⇓ = normalize t₂
                            -- app! , app!⇓ =
                        in {!napp t₁! t₂!!} , {!!}
