{-# OPTIONS --postfix-projections --safe --without-K #-}

module MAV.CutElim (Atom : Set) where

open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (0ℓ; lift; lower; Lift; suc)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as Star

open import MAV.Formula Atom
open import MAV.Base Atom as MAV
import MAV.Symmetric Atom as SMAV

private
  variable
    A A′ : Atom
    P P′ : Formula
    Q Q′ : Formula
    R R′ : Formula
    S S′ : Formula

------------------------------------------------------------------------------
-- Construct the syntactic model from presheaves and chu. We can turn
-- MAV into a *-autonomous category with finite products and
-- coproducts in such a way that we can deduce cut-elimination is
-- admissible.

import Algebra.PreSheaf
import Algebra.Sheaf
import Algebra.Chu

module P = Algebra.PreSheaf MAV.⟶*-Poset
module M = P.LiftIsCommutativePomonoid `⅋-isCommutativePomonoid
module S = Algebra.Sheaf `&-Pomagma
module MS = S.LiftIsCommutativePomonoid `⅋-isCommutativePomonoid `⅋-distrib-`&
module M▷ = S.LiftIsPomonoid `▷-isPomonoid (λ w x y z → `medial ◅ ε) (`tidy ◅ ε)
module D = S.LiftIsDuoidal `⅋-`▷-isDuoidal
                           (λ x y → `⅋-comm ◅ ε , `⅋-comm ◅ ε)
                           `⅋-distrib-`&
                           (λ w x y z → `medial ◅ ε)
                           (`tidy ◅ ε)

open S._≤ˢ_
open S.Sheaf

-- The units of the two monoids are equal (thanks to the tidy rule)
units-iso : MS.εˢ S.≈ˢ M▷.ιˢ
units-iso .proj₁ .*≤ˢ* {x} (t , x≤t) = M▷.ιˢ .≤-closed x≤t (M▷.ιˢ .∨-closed t)
units-iso .proj₂ .*≤ˢ* {x} x≤I = S.leaf (x , x≤I) , ε


module CC = Algebra.Chu.Construction
              MS.⊸ˢ-⊗ˢ-isResiduatedCommutativePomonoid
              S.∧ˢ-isMeetSemilattice
              S.∨ˢ-isJoinSemilattice
              MS.εˢ
    renaming (_⊗_ to _⟦⊗⟧_;
              _⅋_ to _⟦⅋⟧_;
              _&_ to _⟦&⟧_;
              -- _⊕_ to _⟦⊕⟧_;
              I to ⟦I⟧;
              ¬ to ⟦¬⟧) -- hiding (⅋-mono; ⅋-sym)

open CC
open Chu
open _==>_
open CC.SelfDual
      D.⊗ˢ-▷ˢ-isDuoidal
      (S.≤ˢ-trans (M▷.▷ˢ-mono (S.≤ˢ-reflexive units-iso) S.≤ˢ-refl) (S.≤ˢ-reflexive (M▷.▷ˢ-identityˡ _)))
      (S.≤ˢ-reflexive (S.Eq.sym units-iso))

Chu-mix : ⟦I⟧ ≅ ⟦¬⟧ ⟦I⟧
Chu-mix .proj₁ .fpos = S.≤ˢ-refl
Chu-mix .proj₁ .fneg = S.≤ˢ-refl
Chu-mix .proj₂ .fpos = S.≤ˢ-refl
Chu-mix .proj₂ .fneg = S.≤ˢ-refl

I-eq-J : ⟦I⟧ ≅ J
I-eq-J .proj₁ .fpos = S.≤ˢ-reflexive units-iso
I-eq-J .proj₁ .fneg = S.≤ˢ-reflexive (S.Eq.sym units-iso)
I-eq-J .proj₂ .fpos = S.≤ˢ-reflexive (S.Eq.sym units-iso)
I-eq-J .proj₂ .fneg = S.≤ˢ-reflexive units-iso

ChuModel : SMAV.Model (suc (suc 0ℓ)) 0ℓ 0ℓ
ChuModel .SMAV.Model.Carrier = Chu
ChuModel .SMAV.Model._≈_ = _≅_
ChuModel .SMAV.Model._≲_ = _==>_
ChuModel .SMAV.Model.¬ = ⟦¬⟧
ChuModel .SMAV.Model.I = ⟦I⟧
ChuModel .SMAV.Model.J = J
ChuModel .SMAV.Model._⊗_ = _⟦⊗⟧_
ChuModel .SMAV.Model._▷_ = _⍮_
ChuModel .SMAV.Model._&_ = _⟦&⟧_
ChuModel .SMAV.Model.⊗-isCommutativePomonoid = ⊗-isCommutativePomonoid
ChuModel .SMAV.Model.⊗-isStarAutonomous = ⊗-isStarAutonomous
ChuModel .SMAV.Model.mix = Chu-mix
ChuModel .SMAV.Model.&-isMeet = &-isMeet
ChuModel .SMAV.Model.⊗-▷-isDuoidal = ⊗-⍮-isDuoidal
ChuModel .SMAV.Model.I-eq-J = I-eq-J
ChuModel .SMAV.Model.▷-self-dual = self-dual

_>>>_ = ⟶*-trans

-- The atom interaction law in PreSheaves
atom-int : ∀ A → (P.ηᵖ (`- A) M.∙ᵖ P.ηᵖ (`+ A)) P.≤ᵖ P.ηᵖ `I
atom-int A .P.*≤ᵖ* {P} (p₁ , p₂ , p≤p₁p₂ , lift p₁≤a , lift p₂≤-A) .lower =
    p≤p₁p₂ >>> (`⅋-mono p₁≤a p₂≤-A >>> (`⅋-comm ◅ `axiom ◅ ε))

atom : Atom → Chu
atom A .pos = S.α (P.ηᵖ (`- A))
atom A .neg = S.α (P.ηᵖ (`+ A))
atom A .int = S.≤ˢ-trans (MS.α-monoidal .proj₁) (S.α-mono (atom-int A))

open SMAV.Interpretation ChuModel atom

tidyup-lem : (t : S.Tree (Σ[ P ∈ Formula ] (Lift 0ℓ (P ⟶* `I)))) →
             S.⋁ᵗ t ⟶* `I
tidyup-lem (S.leaf (P , lift p⟶*I)) = p⟶*I
tidyup-lem (S.node S t) = `&-mono (tidyup-lem S) (tidyup-lem t) >>> (`tidy ◅ ε)

tidyup : ∀ {P} → MS.εˢ .ICarrier P → P ⟶* `I
tidyup (t , p⟶*t) = p⟶*t >>> tidyup-lem t

mutual
  okada : ∀ P → ⟦ P ⟧ .neg .ICarrier P
  okada `I = S.leaf (`I , lift ε) , ε
  okada (`+ A) = S.leaf (`+ A , lift ε) , ε
  okada (`- A) = S.leaf (`- A , lift ε) , ε
  okada (P `⅋ Q) = S.leaf (P `⅋ Q , P , Q , ε , okada P , okada Q) , ε
  okada (P `⊗ Q) .proj₁ {R} x =
    ⟦ P ⟧ .neg .≤-closed
      ((`switch ◅ ε) >>> ((P `⊗⟩* ((`⅋-comm ◅ ε) >>> okada2 Q R x)) >>> (`⊗-unit ◅ ε)))
      (okada P)
  okada (P `⊗ Q) .proj₂ {R} x =
    ⟦ Q ⟧ .neg .≤-closed
      ((`⊗-comm `⟨⅋ R ◅ `switch ◅ ε) >>> ((Q `⊗⟩* ((`⅋-comm ◅ ε) >>> okada2 P R x)) >>> (`⊗-unit ◅ ε)))
      (okada Q)
  okada (P `& Q) =
    S.node (S.leaf (P , inj₁ (okada P))) (S.leaf (Q , inj₂ (okada Q))) , ε
  okada (P `⊕ Q) =
    ⟦ P ⟧ .neg .≤-closed (`left ◅ ε) (okada P) ,
    ⟦ Q ⟧ .neg .≤-closed (`right ◅ ε) (okada Q)
  okada (P `▷ Q) =
    P , Q , ε , okada P , okada Q

  okada2 : ∀ P R → ⟦ P ⟧ .pos .ICarrier R → (R `⅋ P) ⟶* `I
  okada2 P R ϕ =
    tidyup (⟦ P ⟧ .int .*≤ˢ* {R `⅋ P} (S.leaf (R `⅋ P , R , P , ε , ϕ , okada P) , ε))

-- if 'P′ is provable, then it has A cut-free proof
sem-cut-elim : ∀ P → ⟦I⟧ ==> ⟦ P ⟧ → P ⟶* `I
sem-cut-elim P prf = tidyup (prf ._==>_.fneg .*≤ˢ* {P} (okada P))

cut-elim : (P : Formula) → (P SMAV.⟶* `I) → P ⟶* `I
cut-elim P prf = sem-cut-elim P ⟦ prf ⟧steps
