# Action

A Lean formalisation of higher-rank binding syntax, developed
jointly by Andrej Bauer and Claude (Anthropic).

The approach: model a binding signature as a `Carrier` — a pair of
indexed containers (one for shapes, one for arities) coupled by an
action `γ ⋈ α : Shape` that extends a shape by an arity's binders.
Expressions are the W-type of the shape container with the
recursive child's shape index shifted by the action; this is the
free relative monad of the decorated container.

## File map

| File              | Contents                                                   |
| ----------------- | ---------------------------------------------------------- |
| `Carrier.lean`    | The `Carrier` structure and the `⋈ / ⋈*` action.           |
| `Renaming.lean`   | Arity-respecting slot maps `γ →ʳ δ` between shapes.        |
| `Expr.lean`       | `Expr γ`, the unit `Expr.η`, the renaming action on Expr.  |
| `Subst.lean`      | `Subst`, `Inst`, and the Kleisli extension `lift`.         |
| `SyntaxMonad.lean` | The `RelativeMonad` instance.                             |

