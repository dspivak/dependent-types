```agda
{-# OPTIONS --without-K --rewriting #-}
module part4 where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import part1
open import part2
open import part3
```

# $\Pi$-Types, Jump Monads & Distributive Laws

We have so far considered how polynomial universes may be equipped with structure to interpret the unit type and dependent pair types. We have not yet, however, said much in the way of *dependent function types.* In order to rectify this omission, it will first be prudent to consider some additional structure on the category of polynomial functors – specifically a new functor ${\upuparrows}[\_] : \mathsf{Tw}(\mathbf{Poly}) \times \mathbf{Poly} \to \mathbf{Poly}$ that plays a similar role for `Π` types as the composition $\triangleleft : \mathbf{Poly} \times \mathbf{Poly} \to \mathbf{Poly}$ played for `Σ` types, and which in turn bears a close connection to a class of structured morphisms in $\mathbf{Poly}$, which we refer to as *jump morphisms.*

## The $\upuparrows$ and ${\upuparrows}[\_]$ Functors

The $\upuparrows$ functor can be loosely defined as the solution to the following problem: given a polynomial universe `𝔲`, find `𝔲 ⇈ 𝔲` such that `𝔲` classifies `𝔲 ⇈ 𝔲` if and only if `𝔲` has the structure to interpret `Π` types (in the same way that `𝔲` classifies `𝔲 ◃ 𝔲` if and only if `𝔲` has the structure to interpret `Σ` types). Generalizing this to arbitrary pairs of polynomials $p = (A , B), ~ q = (C , D)$ then yields the following formula for $p \upuparrows q$: $$
p \upuparrows q = \sum_{(a , f) : \sum_{a : A} C^{B(a)}} y^{\prod_{b : B(a)} D(f(b))}
$$

```agda
_⇈_ : ∀ {ℓ ℓ' κ κ'} → Poly ℓ κ → Poly ℓ' κ' → Poly (ℓ ⊔ κ ⊔ ℓ') (κ ⊔ κ')
(A , B) ⇈ (C , D) = 
    ( Σ A (λ a → B a → C) 
    , (λ (a , f) → (b : B a) → D (f b)))
```

Note that this construction is straightforwardly functorial with respect to arbitrary lenses in its 2nd argument. Functoriality of the 1st argument is trickier, however. For reasons that will become apparent momentarily, we define the functorial action $p \upuparrows q \leftrightarrows p' \upuparrows q$ of $\upuparrows$ on a lens $f : p \leftrightarrows p'$ equipped with a left inverse $f' : p' \leftrightarrows p$, i.e. such that $f' \circ f = \text{id}_p$.

```agda
⇈Lens : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
        → (p : Poly ℓ κ) (q : Poly ℓ' κ') 
        → (r : Poly ℓ'' κ'') (s : Poly ℓ''' κ''')
        → (f : p ⇆ r) (f' : r ⇆ p) 
        → EqLens p p (id p) (comp p r p f f')
        → (g : q ⇆ s) → (p ⇈ q) ⇆ (r ⇈ s)
⇈Lens p q r s (f , f♯) (f' , f'♯) e (g , g♯) = 
    ( (λ (a , γ) → (f a , (λ x → g (γ (f♯ a x)))))
    , λ (a , γ) Ϝ x → g♯ (γ x) (transp (λ y → snd s (g (γ y))) (sym (snd (e a) x)) (Ϝ (f'♯ (f a) (transp (snd p) (fst (e a)) x)))))
```

By construction, the existence of a Cartesian lens `(π , π♯) : 𝔲 ◃ 𝔲 ⇆ 𝔲` effectively shows that `𝔲` is closed under `Π`-types, since:

* `π` maps a pair `(A , B)` consisting of `A : 𝓤` and `B : u(A) → 𝓤` to a term `π(A,B)` representing the corresponding `Π` type. This corresponds to the type formation rule $$ \inferrule{\Gamma \vdash A : \mathsf{Type}\\ \Gamma, x : A \vdash B[x] ~ \mathsf{Type}}{\Gamma \vdash \Pi x : A . B[x] ~ \mathsf{Type}} $$
* The "elimination rule" `π♯ (A , B)`, for any pair `(A , B)` as above, maps an element `f : π(A,B)` to a function `π♯ (A , B) f : (a : u(A)) → u (B x)` which takes an element `x` of `A` and yields an element of `B x`. This corresponds to the rule for function application: $$
\inferrule{\Gamma \vdash f : \Pi x : A . B[x]\\ \Gamma \vdash a : A}{\Gamma \vdash f ~ a : B[a]}
$$
* Since `π♯ (A , B)` is an equivalence, it follows that there is an inverse `π♯⁻¹ (A , B) : ((x : u(A)) → u(B(x)) → u(π(A,B))`, which corresponds to $\lambda$-abstraction: $$
\inferrule{\Gamma, x : A \vdash f[x] : B[x]}{\Gamma \vdash \lambda x . f[x] : \Pi x : A . B[x]}
$$
* The fact that `π♯⁻¹ (A , B)` is both a left and a right inverse to `π♯` then corresponds to the $\beta$ and $\eta$ laws for `Π` types. $$
(\lambda x . f[x]) ~ a = f[a] \qquad f = \lambda x . f ~ x
$$

Although it is clear enough that the $\upuparrows$ functor serves its intended purpose of characterizing `Π` types in polynomial universes, its construction seems somewhat more ad hoc than that of $\triangleleft$, which similarly characterized `Σ` types in polynomial universes while arising quite naturally from composition of polynomial functors. We would like to better understand what additional properties $\upuparrows$ must satisfy, and how these in turn are reflected as properties of polynomial universes with `Π` types. In fact, we will ultimately show that this construction is intimately linked with a quite simple structure on polynomial universes `𝔲`, namely a *distributive law* of `𝔲` (viewed as a monad) over itself, satisfying some additional requirements. Before that, however, we note some other key properties of $\upuparrows$.

Specifically, let $\mathbf{Poly}_{R}$ be the wide subcategory of $\mathbf{Poly}$ spanned by morphisms equipped with left inverses (hence which are themselves right inverses). Straightforwardly, $\triangleleft$ restricts to a monoidal product on $\mathbf{Poly}_R$, since it is functorial in both arguments and must preserve left/right inverses. Hence $\upuparrows$ can be viewed as a functor $\mathbf{Poly}_R \times \mathbf{Poly} \to \mathbf{Poly}$. Then $\upuparrows$ moreover naturally carries the structure of an *action* on $\mathbf{Poly}$ of the monoidal category $\mathbf{Poly}_R$ equipped with $\triangleleft$, in that there are natural isomorphisms $$
\mathbb{y} \upuparrows p \simeq p $$ $$
(p \triangleleft q) \upuparrows r \simeq p \upuparrows (q \upuparrows r)
$$

```agda
𝕪⇈ : ∀ {ℓ κ} (p : Poly ℓ κ) → (𝕪 ⇈ p) ⇆ p
𝕪⇈ p = ( (λ (tt , a) → a tt) 
       , λ (tt , a) b tt → b)

𝕪⇈Vert : ∀ {ℓ κ} (p : Poly ℓ κ) → isVertical (𝕪 ⇈ p) p (𝕪⇈ p)
𝕪⇈Vert p = Iso→isEquiv ( (λ x → tt , (λ tt → x)) 
                       , ( (λ a → refl) 
                       , λ b → refl))

𝕪⇈Cart : ∀ {ℓ κ} (p : Poly ℓ κ) → isCartesian (𝕪 ⇈ p) p (𝕪⇈ p)
𝕪⇈Cart p (tt , x) = 
    Iso→isEquiv ( (λ Ϝ → Ϝ tt) 
                , ( (λ a → refl) 
                  , λ b → refl))

⇈Curry : ∀ {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2}
         → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2)
         → ((p ◃ q) ⇈ r) ⇆ (p ⇈ (q ⇈ r))
⇈Curry p q r = ( (λ ((a , h) , k) → a , (λ b → (h b) , (λ d → k (b , d)))) 
               , λ ((a , h) , k) f (b , d) → f b d)

⇈CurryVert : ∀ {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2}
             → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2)
             → isVertical ((p ◃ q) ⇈ r) (p ⇈ (q ⇈ r)) (⇈Curry p q r)
⇈CurryVert p q r = 
    Iso→isEquiv ((λ (a , h) → (a , (λ x → fst (h x))) , (λ (x , y) → snd (h x) y)) 
                , ( (λ a → refl) 
                  , λ b → refl))

⇈CurryCart : ∀ {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2}
             → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2)
             → isCartesian ((p ◃ q) ⇈ r) (p ⇈ (q ⇈ r)) (⇈Curry p q r)
⇈CurryCart p q r ((a , h) , k) = 
    Iso→isEquiv ( (λ f b d → f (b , d)) 
                , ( (λ f → refl) 
                  , λ f → refl))
```

Moreover, $\upuparrows$ is colax with respect to $\triangleleft$ in its second argument, in that there are natural transformations $$
p \upuparrows \mathbb{y} → \mathbb{y}
$$ $$
p \upuparrows (q \triangleleft r) \to (p \upuparrows q) \triangleleft (p \upuparrows r)
$$

```agda
⇈𝕪 : ∀ {ℓ κ} (p : Poly ℓ κ) → (p ⇈ 𝕪) ⇆ 𝕪
⇈𝕪 p = ( (λ (a , γ) → tt) 
       , λ (a , γ) tt b → tt )

⇈Distr : ∀ {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2}
         → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2)
         → (p ⇈ (q ◃ r)) ⇆ ((p ⇈ q) ◃ (p ⇈ r))
⇈Distr p q r = ( (λ (a , h) → (a , (λ b → fst (h b))) , λ f → a , (λ b → snd (h b) (f b))) 
               , λ (a , h) (f , g) b → (f b) , (g b) )
```

Moreover, both of these natural transformations are Cartesian.

```agda
⇈𝕪Cart : ∀ {ℓ κ} (p : Poly ℓ κ) → isCartesian (p ⇈ 𝕪) 𝕪 (⇈𝕪 p)
⇈𝕪Cart p (x , γ) = 
    Iso→isEquiv ( (λ x → tt) 
                , ( (λ a → refl) 
                  , λ b → refl))

⇈DistrCart : ∀ {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2}
             → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2)
             → isCartesian (p ⇈ (q ◃ r)) ((p ⇈ q) ◃ (p ⇈ r)) (⇈Distr p q r)
⇈DistrCart p q r (a , h) =
    Iso→isEquiv ( (λ f → (λ b → fst (f b)) , (λ b → snd (f b))) 
                , ( (λ (f , g) → refl) 
                  , λ f → refl))
```

The fact that `⇈Distr` is Cartesian corresponds to the distributive law of `Π` types over `Σ` types, i.e. $$
\Pi x : A . \Sigma y : B[x] . C[x,y] \simeq \Sigma f : \Pi x : A . B[x] . \Pi x : A . C[x, f(x)]
$$ One may wonder, then, whether this distributive law is somehow related to a distributive law ofg the monad structure on a polynomial universe 𝔲 given by Σ types (as discussed in the previous section) over itself, i.e. a morphism $$ \mathfrak{u} \triangleleft \mathfrak{u} \leftrightarrows \mathfrak{u} \triangleleft \mathfrak{u} $$ subject to certain laws. This is in fact the case, but showing as much requires some more work.

As a first step in this direction, we make a perhaps unexpected move of further generalizing the $\upuparrows$ functor to a functor $\mathsf{Tw}(\mathbf{Poly}) \times \mathbf{Poly} \to \mathbf{Poly}$, where $\mathsf{Tw}(\mathbf{Poly})$ is the *twisted arrow category* of $\mathbb{Poly}$, i.e. the category whose objects are lenses and whose morphisms are *twisted* commuting squares of the form $$
\begin{array}{ccc}
p & \leftrightarrows q\\
\donwuparrows & & \downuparrows\\
r & \rightleftarrows & s
\end{array}
$$

```agda
_⇈[_][_]_ : ∀ {ℓ ℓ' ℓ'' κ κ' κ''}
            → (p : Poly ℓ κ) (q : Poly ℓ' κ')
            → (p ⇆ q) → (r : Poly ℓ'' κ'')
            → Poly (ℓ ⊔ κ ⊔ ℓ'') (κ' ⊔ κ'')
(A , B) ⇈[ (C , D) ][ (f , f♯) ] (E , F) =
   ( (Σ A (λ a → B a → E)) 
   , (λ (a , ε) → (d : D (f a)) → F (ε (f♯ a d))))

⇈[]Lens : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 ℓ5 κ0 κ1 κ2 κ3 κ4 κ5}
          → (p : Poly ℓ0 κ0) (p' : Poly ℓ3 κ3)
          → (q : Poly ℓ1 κ1) (q' : Poly ℓ4 κ4)
          → (r : Poly ℓ2 κ2) (r' : Poly ℓ5 κ5)
          → (f : p ⇆ q) (f' : p' ⇆ q')
          → (g : p ⇆ p') (h : q' ⇆ q) (k : r ⇆ r')
          → EqLens p q f (comp p p' q g (comp p' q' q f' h))
          → (p ⇈[ q ][ f ] r) ⇆ (p' ⇈[ q' ][ f' ] r')
⇈[]Lens p p' q q' r r' (f , f♯) (f' , f'♯) (g , g♯) (h , h♯) (k , k♯) e = 
    ( (λ (a , γ) → (g a , λ x → k (γ (g♯ a x)))) 
    , λ (a , γ) Ϝ x → k♯ (γ (f♯ a x)) (transp (λ y → snd r' (k (γ y))) (sym (snd (e a) x)) (Ϝ (h♯ (f' (g a)) (transp (snd q) (fst (e a)) x)))) )

⇈[-][-]Lens : ∀ {ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓ''''' κ κ' κ'' κ''' κ'''' κ'''''}
              → (p : Poly ℓ κ) (q : Poly ℓ' κ')
              → (p' : Poly ℓ'' κ'') (q' : Poly ℓ''' κ''')
              → (r : Poly ℓ'''' κ'''') (r' : Poly ℓ''''' κ''''')
              → (f : p ⇆ q) (f' : p' ⇆ q')
              → (g : p ⇆ p') (h : q ⇆ q')
              → (k : r ⇆ r')
              → isCartesian q q' h
              → EqLens p q' (comp p q q' f h) (comp p p' q' g f')
              → (p ⇈[ q ][ f ] r) ⇆ (p' ⇈[ q' ][ f' ] r')
⇈[-][-]Lens p q p' q' r r' 
            (f , f♯) (f' , f'♯) (g , g♯) (h , h♯) (k , k♯) ch e =
    ( (λ (a , γ) → g a , λ b → k (γ (g♯ a b))) 
    , λ (a , γ) Ϝ d
        → k♯ (γ (f♯ a d))
             (transp (snd r') (ap k (ap γ 
                     ((g♯ a (f'♯ (g a) (transp (snd q') (fst (e a)) 
                                      (inv (ch (f a)) d)))) 
                     ≡〈 (sym (snd (e a) (inv (ch (f a)) d))) 〉 
                     ((f♯ a (h♯ (f a) (inv (ch (f a)) d))) 
                     ≡〈 (ap (f♯ a) (snd (snd (ch (f a))) d)) 〉 
                     ((f♯ a d) □)))))
                 (Ϝ (transp (snd q') (fst (e a)) 
                            (inv (ch (f a)) d)))) )

postulate
    funext : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {f g : (x : A) → B x}
             → ((x : A) → f x ≡ g x) → f ≡ g
    funextr : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {f g : (x : A) → B x}
              → (e : (x : A) → f x ≡ g x) → coAp (funext e) ≡ e
    funextl : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {f g : (x : A) → B x}
              → (e : f ≡ g) → funext (coAp e) ≡ e

transpD : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {a a' : A}
          → (f : (x : A) → B x) (e : a ≡ a')
          → transp B e (f a) ≡ f a'
transpD f refl = refl

transpHAdj : ∀ {ℓ ℓ' κ} {A : Type ℓ} {B : Type ℓ'} 
            → {C : B → Type κ} {a : A}
            → {g : A → B} {h : B → A} 
            → (f : (x : A) → C (g x)) 
            → (e : (y : B) → g (h y) ≡ y)
            → (e' : (x : A) → h (g x) ≡ x)
            → (e'' : (x : A) → e (g x) ≡ ap g (e' x))
            → transp C (e (g a)) (f (h (g a))) ≡ f a
transpHAdj {C = C} {a = a} {g = g} {h = h} f e e' e'' = 
    transp C (e (g a)) (f (h (g a)))               
        ≡〈 ap (λ ee → transp C ee (f (h (g a)))) (e'' a) 〉 
    (transp C (ap g (e' a)) (f (h (g a))) 
        ≡〈 sym (transpAp C g (e' a) (f (h (g a)))) 〉 
    ((transp (λ x → C (g x)) (e' a) (f (h (g a)))) 
        ≡〈 transpD f (e' a) 〉
    ((f a) □)))

PreCompEquiv : ∀ {ℓ ℓ' κ} {A : Type ℓ} {B : Type ℓ'} {C : B → Type κ}
               → (f : A → B) → isEquiv f 
               → isEquiv {A = (b : B) → C b} 
                         {B = (a : A) → C (f a)} 
                         (λ g → λ a → g (f a))
PreCompEquiv {C = C} f ef =
    let (f⁻¹ , l , r , e) = Iso→HAdj (isEquiv→Iso ef) 
    in Iso→isEquiv ( (λ g b → transp C (r b) (g (f⁻¹ b))) 
                   , ( (λ g → funext (λ b → transpD g (r b))) 
                     , λ g → funext (λ a → transpHAdj g r l (λ x → sym (e x)))))

PostCompEquiv : ∀ {ℓ κ κ'} {A : Type ℓ} {B : A → Type κ} {C : A → Type κ'}
                → (f : (x : A) → B x → C x) → ((x : A) → isEquiv (f x))
                → isEquiv {A = (x : A) → B x} 
                          {B = (x : A) → C x}
                          (λ g x → f x (g x))
PostCompEquiv f ef = 
    ( ( (λ g x → fst (fst (ef x)) (g x))
      , λ g → funext (λ x → snd (fst (ef x)) (g x))))
    , ( (λ g x → fst (snd (ef x)) (g x)) 
      , λ g → funext (λ x → snd (snd (ef x)) (g x)))

syminvol : ∀ {ℓ} {A : Type ℓ} {a b : A}
           → (e : a ≡ b) → sym (sym e) ≡ e
syminvol refl = refl
{-# REWRITE syminvol #-}

{- ⇈[]Lens≡ : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 κ0 κ1 κ2 κ3}
           → (p : Poly ℓ0 κ0) (p' : Poly ℓ2 κ2)
           → (q : Poly ℓ1 κ1) (q' : Poly ℓ3 κ3)
           → (f : p ⇆ p') (g : q ⇆ q')
           → (cf : isCartesian p p' f)
           → EqLens (p ⇈ q) (p' ⇈ q')
                    (⇈Lens p q p' q' f cf g)
                    (⇈[]Lens p p' p p' q q' (id p) (id p') f (Cart→Chart p p' f cf) g (λ a → refl , (λ d → sym (snd (snd (cf a)) d))))
⇈[]Lens≡ p p' q q' f g cf = λ a → refl , (λ b → refl) -}
```

Straightforwardly, we have that `p ⇈ q = p ⇈[ p ][ id p ] q`. In particular, we have `⇈Lens p p' q q' f f' e g = ⇈[]Lens p p' p p' q q' (id p) (id p') f f' g e`, which serves to motivate the definition of `⇈Lens` in terms of morphism equipped with left inverses.

Moreover, all the properties of `_⇈_` noted above generalize to `_⇈[_][_]_`. For instance, we now have natural isomorphisms $$
\mathbb{y} {\upuparrows}[\text{id}_{\mathbb{y}}] p \simeq p
$$ $$
(p \triangleleft r) {\upuparrows}[f \triangleleft g] q \simeq p {\upuparrows}[f] (r {\upuparrows}[g] q)
$$

And similarly, we have Cartesian natural transformations $$
p {\upuparrows}[f] \mathbb{y} → \mathbb{y}
$$ $$
p {\upuparrows}[g \circ f] (r \triangleleft s) \to (p {\upuparrows}[f] r) \triangleleft (q {\upuparrows}[g] s)
$$

To see why this construction is important, we now introduce the novel concept of a *jump morphism* in $\mathbf{Poly}$.

## Jump Morphisms

Given a lens $(f , f^\sharp) : p \leftrightarrows q$ with $p = (A , B)$ and $q = (C , D)$, a *jump morphism* $(g, g^\sharp) : r \xrightarrow{p \xrightarrow{(f , f^\sharp)} q} s$ for $r = (A' , B')$ and $s = (C' , D')$ is a lens $(g, g^\sharp) : p \triangleleft r \leftrightarrows s \triangleleft q$ equipped with identities `\pi_2(g(a , h)(d')) = f(a)` for all $a : A$ with $h : {A'}^{B(a)}$ and $d' : D'(\pi_1(g(a,h)))$, and $\pi_1(g^\sharp(a,h)(d',d)) = f^\sharp(a , d)$ for all $a : A$ with $h : {A'}^{B(a)}$ and $d : D(f(a))$ and $d' : D'(g(a , h))$.

```agda
Jump : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
       → (p : Poly ℓ κ) (q : Poly ℓ' κ')
       → (r : Poly ℓ'' κ'') (s : Poly ℓ''' κ''')
       → (p ⇆ q)
       → (p ◃ r) ⇆ (s ◃ q)
       → Set (ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ κ ⊔ κ' ⊔ κ''')
Jump (A , B) (C , D) (A' , B') (C' , D') (f , f♯) (g , g♯) =
    Σ ((a : A) (h : B a → A') 
       (d' : D' (fst (g (a , h)))) 
        → snd (g (a , h)) d' ≡ f a) 
       λ e → (a : A) (h : B a → A') 
             (d' : D' (fst (g (a , h))))
             (d : D (snd (g (a , h)) d'))
             → fst (g♯ (a , h) (d' , d)) 
               ≡ f♯ a (transp D (e a h d') d)
```

By application of function extensionality, we have the following type of equality proofs for jump morphisms:

```agda
transpComp : ∀ {ℓ κ} {A : Type ℓ} {a b c : A} {B : A → Type κ}
             → (e1 : a ≡ b) (e2 : b ≡ c) (x : B a)
             → transp B e2 (transp B e1 x)
               ≡ transp B (a ≡〈 e1 〉 e2) x
transpComp refl refl x = refl

_•_ : ∀ {ℓ} {A : Type ℓ} {a b c : A}
      → (a ≡ b) → (b ≡ c) → (a ≡ c)
refl • refl = refl

comprewrite : ∀ {ℓ} {A : Type ℓ} {a b c : A}
              → (e1 : a ≡ b) (e2 : b ≡ c)
              → (a ≡〈 e1 〉 e2) ≡ (e1 • e2)
comprewrite refl refl = refl

{-# REWRITE comprewrite #-}

EqJump1 : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
          → (p : Poly ℓ κ) (q : Poly ℓ' κ')
          → (r : Poly ℓ'' κ'') (s : Poly ℓ''' κ''')
          → (g g' : (p ◃ r) ⇆ (s ◃ q))
          → Set (ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ ℓ''' ⊔ κ ⊔ κ' ⊔ κ'' ⊔ κ''')
EqJump1 (A , B) (C , D) (A' , B') (C' , D') (g , g♯) (g' , g'♯) =
    (a : A) (h : B a → A')
    → Σ (fst (g (a , h)) ≡ fst (g' (a , h)))
        (λ e1 → (d' : D' (fst (g (a , h))))
              → Σ ((snd (g (a , h)) d' ≡ snd (g' (a , h)) (transp D' e1 d')))
                  (λ e2 → (d : D (snd (g (a , h)) d'))
                        → Σ (fst (g♯ (a , h) (d' , d)) ≡ fst (g'♯ (a , h) (transp D' e1 d' , transp D e2 d)))
                            λ e3 → transp (λ x → B' (h x)) e3 (snd (g♯ (a , h) (d' , d))) 
                                   ≡ snd (g'♯ (a , h) (transp D' e1 d' , transp D e2 d))))

EqJump2 : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
          → (p : Poly ℓ κ) (q : Poly ℓ' κ')
          → (r : Poly ℓ'' κ'') (s : Poly ℓ''' κ''')
          → (f : p ⇆ q)
          → (g g' : (p ◃ r) ⇆ (s ◃ q))
          → EqJump1 p q r s g g'
          → Jump p q r s f g → Jump p q r s f g'
          → Set (ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ κ ⊔ κ' ⊔ κ''')
EqJump2 (A , B) (C , D) (A' , B') (C' , D') (f , f♯)
        (g , g♯) (g' , g'♯) ej (e , e♯) (e' , e'♯) =
    (a : A) (h : B a → A') (d' : D' (fst (g (a , h)))) →
    let (e1 , ej2) = ej a h in
    let (e2 , ej3) = ej2 d' in
    Σ ((e2 • (e' a h (transp D' e1 d'))) ≡ e a h d')
      (λ e5 → (d : D (snd (g (a , h)) d'))
              → ((fst (ej3 d)) • ((e'♯ a h (transp D' e1 d') (transp D e2 d)) • (ap (f♯ a) ((transpComp e2 (e' a h (transp D' e1 d')) d) • (ap (λ ee → transp D ee d) e5))))) ≡ e♯ a h d' d)
```

We can think of a jump morphism $g : r \xrightarrow{p \xrightarrow{f} q} s$ as one which applies $f$ to the components of $p$ and $q$ while *jumping over* its action on the components of $r$ and $s$.