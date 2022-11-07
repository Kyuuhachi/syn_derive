A simple crate for reducing the boilerplate when writing parsers with [`syn`].

## Structs

```rust
#[derive(Clone, Debug, syn_derive::Parse, syn_derive::ToTokens)]
struct ExampleStruct {
	#[parse(Attribute::parse_outer)]
	#[to_tokens(|tokens, val| tokens.append_all(val))]
	attrs: Vec<Attribute>,

	path: Path,

	#[syn(parenthesized)]
	paren_token: Paren,

	#[syn(in = brace_token)]
	#[parse(Punctuated::parse_terminated)]
	args: Punctuated<Box<Expr>, Token![,]>,

	semi_token: Token![;],
}
```

`#[syn(parenthesized)]`,
`#[syn(braced)]`,
`#[syn(bracketed)]`:
  Corresponds to the isonymous macros in `syn`.
  Must be attached to [`struct@Paren`], [`struct@Brace`], and [`struct@Bracket`] fields, respectively.

`#[syn(in = paren_token)]`:
  The field is read from inside the named delimiter pair.

`#[parse(expr)]`:
  A function used to parse the field,
  often used with [`Punctuated::parse_terminated`]
  or [`Attribute::parse_outer`].

`#[to_tokens(expr)]`:
  A function used to tokenize the field.
  Often used with [`TokenStreamExt::append_all`],
  though for type resolution reasons this needs to be indirected through a closure expression.

## Enums

```rust
#[derive(Clone, Debug, syn_derive::Parse, syn_derive::ToTokens)]
enum ExampleEnum {
	#[parse(peek = |i| i.peek(Token![struct]))]
	Struct(ItemStruct),
	#[parse(peek = |i| i.peek(Token![enum]))]
	Enum(ItemEnum),

	Other {
		path: Path,
		semi_token: Token![;],
	}
}
```

`#[parse(peek = expr)]`:
  Checks whether the variant should be parsed.
  Even if multiple peeks succeed, only the first successful variant is attempted.

Enum parsing is unstable and may change without warning.

# Alternatives
- [`derive-syn-parse`](https://docs.rs/derive-syn-parse/latest/)
  does not handle [`ToTokens`].
  It also seems to encourage throwing tokens away with its `prefix` and `postfix` attributes.
  It does give slightly better error messages on enums than `syn_derive`, however.
- [`parsel`](https://docs.rs/derive-syn-parse/latest/)
  uses its own types for parentheses, meaning the AST types have different API from [`syn`]'s own.
