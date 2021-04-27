{-# OPTIONS --without-K --safe --show-implicit #-}
open import Categories.Category

module Categories.Category.Pretopos {o ℓ e} (𝒞 : Category o ℓ e) where
open import Level
open import Function using (_$_; flip)
open import Data.Product using (Σ; _,_; uncurry)
open import Relation.Binary using (Poset)

-- open import Categories.Functor renaming (id to idF)
-- open import Categories.Functor.Bifunctor
-- open import Categories.NaturalTransformation hiding (id)
-- open import Categories.NaturalTransformation.Properties
-- open import Categories.Category.Cartesian 𝒞
-- open import Categories.Category.Monoidal.Closed
-- open import Categories.Object.Product 𝒞
--   hiding (repack≡id; repack∘; repack-cancel; up-to-iso; transport-by-iso)
-- open import Categories.Object.Exponential 𝒞 hiding (repack)
open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Category.Complete.Finitely 𝒞 using (FinitelyComplete)
open import Categories.Category.Regular
open import Categories.Object.Product 𝒞 using (Product)
open import Categories.Object.Subobject 𝒞 using (Subobjects)

private
  module 𝒞 = Category 𝒞
  open Category 𝒞
  open HomReasoning
  open Equiv
  variable
    A B C   : Obj
    f g h i : A ⇒ B

-- Regular is in the library
open Product using (A×B)
record InternalEquivRel (pf : FinitelyComplete) (X : Obj) : Set (suc $ o ⊔ ℓ ⊔ e) where
  open FinitelyComplete

  field
    R : (Subobjects (( pf ×  X) X)).Poset.Carrier -- TODO : why does this look so gross
