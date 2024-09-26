```agda
{-# OPTIONS --without-K --rewriting #-}
module part6v2 where

open import part1v2
open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import part2v2
open import appendixA
open import part3v2
open import Agda.Builtin.Nat
open import part4v2
open import part5v2
```

# Further Structures on Polynomial Universes

In closing, we turn to briefly consider whether and how some additional type-theoretic constructs may be defined for natural models / polynomial universes in the language of polynomial functors, starting with the concept of a universe itself.

## The Shift Operator & Universes

Throughout this paper, we have made extensive use of universes of types. A natural question to ask, then, is when the type theory presented by a polynomial universe itself contains another such universe as a type within itself.

For this purpose, let `𝔳 , 𝔲` be polynomial universes with `𝔳 = (𝓥 , El𝓥)` and `𝔲 = (𝓤 , El)`. If there is a (necessarily unique) Cartesian morphism `𝔳 ⇆ 𝔲`, then it follows that every type family classified by `𝔳` is also classified by `𝔲`, by composition of Cartesian morphisms. However, what we want in this case is the stronger property that `𝔳` is somehow represented as a type within `𝔲`.

For this purpose, we define the following *shift* functor $\poly^{op} \to \poly$ that takes a polynomial `p = (A , B)` to the polynomial `shift p = (⊤ , λ _ → A)`n`:

```agda
shift : ∀ {ℓ κ} → Poly ℓ κ → Poly lzero ℓ
shift (A , _) = (⊤ , λ _ → A)

shiftFunctor : ∀ {ℓ0 κ0 ℓ1 κ1} {p : Poly ℓ0 κ0} {q : Poly ℓ1 κ1}
               → p ⇆ q → shift q ⇆ shift p
shiftFunctor (f , _) = ( (λ _ → tt) , (λ _ → f) )
```

By construction, then, if there is a Cartesian morphism `(v , v♯) : shift (𝓥 , El𝓥) ⇆ (𝓤 , El𝓤)`, it follows that:

* There is a type `v tt : 𝓤`; type theoretically, this corresponds to a type formation rule of the form $$
\inferrule{~}{\Gamma \vdash \mathcal{V} ~ \mathsf{Type}}
$$ We think of `𝓥` as a type whose elements are "codes" for other types.
* There is a function `v♯ tt : El𝓤 (v tt) → 𝓥`, corresponding to the rule $$
\inferrule{\Gamma \vdash e : 𝓥}{\Gamma \vdash \lceil e \rceil ~ \mathsf{Type}}
$$ which decodes a code contained in `𝓥` to its corresponding type.
* There is a function `v♯⁻¹ tt : 𝓥 → El𝓤 (v tt)`, corresponding to the rule $$
\inferrule{\Gamma \vdash T ~ \mathsf{Type}\\ T ~ \text{is classifed by} ~ \mathfrak{v}}{\Gamma \vdash \lfloor T \rfloor : \mathcal{V}}
$$ that assigns a code to each type classified by `𝔳` (note that this restriction to types classified by `𝔳` is necessary to avoid the paradoxes that would arise from having a type universe that contained itself.)
* Such that the following equations hold $$
\lceil \lfloor T \rfloor \rceil = T \qquad e = \lfloor \lceil e \rceil \rfloor
$$

\footnote{Following Gratzer et al., we refer to a universe defined in this way as a universe *a la Coquand.*}

## The $(-)^=$ Operator & Extensional Identity Types

Another key construct of dependent type theory which has figured prominently in the foregoing development of polynomial universes, but which we have not yet shown how to internalize in such universes, is the construction of *identity types*. To some extent, this choice has been deliberate, as the theory of identity types is arguably one of the most complex aspects of dependent type theory, as evidenced by the fact that research into this topic ultimately precipitated the development of homotopy type theory. For this very reason, however, an account of the semantics of dependent type theory without at least some indication of its application to the theory of identity types would be incomplete.

Readers familiar with dependent type theory may be aware that an initial complication posed by the theory of identity types is that these types come in two flavors: extensional and intensional. Extensional identity types reflect propositional equality (i.e. the existence of an inhabitant for the type `a ≡ b`) into judgmental equality (i.e. the metatheoretic proposition that `a = b`) and additionally regard all such proofs of identity as themselves identical. It follows that these identity types carry none of the homotopical information afforded by the alternative – intensional identity types, which are the sort which we have so far used in this paper. However, when working within such a homotopical framework, wherein metatheoretic equality need not be a mere proposition, there exists the possibility of defining extensional identity types in a polynomial universe so as to enable the aforementioned reflection while still allowing proofs of identity to carry higher-dimensional data.

For this purpose, let `p = (A , B)` be some polynomial classified by a polynomial universe `𝔲 = (𝓤 , El)`, i.e. there exists a Cartesian morphism `p ⇆ 𝔲`. We wish to establish under what conditions `𝔲` would also contain "identity types" for `p` allowing a reflection-rule as above. Solving this problem in essentially the same manner as led to the definiiton of the `⇈` functor in the previous section yields the following construction, that maps `p = (A , B)` to the polynomial `p⁼ = (Σ A (λ a → B a × B a) , λ (_ , (b1 , b2)) → b1 ≡ b2)`.

```agda
_⁼ : ∀ {ℓ κ} → Poly ℓ κ → Poly (ℓ ⊔ κ) κ
(A , B)⁼ = (Σ A (λ a → B a × B a) , λ (_ , (b1 , b2)) → b1 ≡ b2)
```

If there is a Cartesian morphism `(ε , ε♯) : (A , B)⁼ ⇆ (𝓤 , El)` then:

* For each type represented by some `a : A` with elements `b1 , b2 : B a`, there is a type `Eq(b1 , b2) : 𝓤`. Type theoretically, this corresponds to the type formation rule $$
\inferrule{\Gamma \vdash T ~ \mathsf{Type}\\ \Gamma \vdash t_1 : T\\ \Gamma \vdash t_2 : T}{\Gamma \vdash t_1 \equiv_A t_2 ~ \mathsf{Type}}
$$
* For each `a : A` and `b1 , b2 : B a` as above, there is a function `El (Eq(b1 , b2)) → b1 ≡ b2` corresponding to the *reflection rule* $$
\inferrule{\Gamma \vdash e : a_0 \equiv_A a_1}{\Gamma \vdash a_0 = a_1}
$$ that converts an inhabitant of the propositional equality into the corresponding judgmental equality.
* ...
* Such that the above two rules are mutually inverse.

What is missing from the above description of extensional identity types is the following rule $$
\inferrule{\Gamma \vdash e_1 : a \equiv_A b\\ \Gamma \vdash e_2 : a \equiv_A b}{\Gamma \vdash e_1 = e_2}
$$ which says that all inhabitants of the identity type are themselves identical (i.e. the identity type is a *mere proposition*). This rule would be validated if we additionally required `𝔲` to have the property that, for all types `A : 𝓤`, the type `El A` is a set (hence for any `a b : El A`, the type `a ≡ b` is a mere proposition.) However, if we do not make this requirement, this opens the possibility of having a model of extensional type theory, modulo the above rule, wherein proofs of equality still carry homotopical information – a potentially new direction in research on the semantics of identity types.

### A Note on Intensional Identity Types & Inductive Types

Attempting to account for *intensional* rather than *extensional* identity types in the language of polynomial functors is rather more complicated, however. As mentioned in Section 2, the inhabitants of intensional identity types are inductively generated from the constructor `refl`, corresponding to reflexivity. The problem with such inductive generation of data from constructors -- from the point of view taken in this paper -- is that it characterizes types in terms of their introduction forms, rather than their elimination forms. In type theoretic jargon, we say that intensional identity types, and inductive types more generally are *positive,* whereas all of the types we have considered so far are *negative,* in that they are characterized by their elimination forms. The universal properties of such negative types are therefore *mapping-in* properties, which are naturally described in terms of presheaves, which we have taken as our intended model for the development of this paper. By contrast, however, the universal properties of positive types are given by *mapping-out* properties, which are rather described in terms of (the opposite category of) *co-presheaves.*

As an illustrative example, let us consider the rather simpler case of (binary) coproducts, which are naturally regarded as positive types characterized by the left and right injections `A → A + B` and `B → A + B`. one might think to define binary coproducts on a polynomial universe `𝔲` in the following way:

The *product* of two polynomial functors $p = \sum_{a : A} y^{B[a]}$ and $q = \sum_{c : C} y^{D[c]}$ can be calculated as follows: $$
\begin{array}{rl} & \left( \sum_{a : A} y^{B[a]} \right) \times \left( \sum_{c : C} y^{D[c]} \right)\\
\simeq & \sum_{(a , c) : A \times C} y^{B[a]} \times y^{D[c]}\\
\simeq & \sum_{(a , c) : A \times C} y^{B[a] + D[c]}
\end{array}
$$ Hence one might think to define binary coproducts on a polynomial universe `𝔲 = (𝓤 , El)` by asking there to be a Cartesian morphism `𝔲 × 𝔲 ⇆ 𝔲`, since this would mean that for every pair of types `(A , B) : 𝓤 × 𝓤`, there is a type `plus(A , B) : 𝓤` such that  `El(plus(A , B)) ≃ El A + El B`.

However, from the perspective of natural models, this condition is too strong. Given a category of contexts $\mathcal{C}$, the category $\widehat{\mathcal{C}}$ of presheaves on $\mathcal{C}$ is the free cocompletion of $\mathcal{C}$, which means that requiring $\mathcal{C}$ to be closed under taking binary coproducts in $\widehat{\mathcal{C}}$ means not only that $\mathcal{C}$ has all binary coproducts, but that in fact all such coproducts in $\mathcal{C}$ are *free.*

Hence it remains to be seen if there can be found a general way of correctly expressing such "positive" type-theoretic concepts as for polynomial universes and natural models in the language of polynomial functors. We hope to continue investigations into these and related questions in future work.

## Conclusion

In this paper, we have advanced a simplified and unified account of the categorical semantics of dependent type theory by expressing the core concepts of natural models entirely within the framework of polynomial functors in HoTT. By utilizing HoTT, we have been able strike an ideal balance between issues of strictness and higher-dimensional coherence that have bedeviled previous accounts. This shift not only streamlines the presentation of the semantics of dependent type theory, but also reveals additional structures thereof, such as the self-distributive law governing the interaction between dependent products and sums.

However, there remain many open questions regarding the further development of this framework, particularly with respect to *positive* type-theoretic constructs such as coproducts, inductive types, and intensional identity types. Further work is needed to explore whether polynomial functors can provide a fully general account of these concepts. We look forward to continuing these investigations, with the aim of extending the unification presented here to encompass a wider range of type-theoretic phenomena.