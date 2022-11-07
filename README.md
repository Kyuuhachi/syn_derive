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

<code>#[syn([`parenthesized`])]</code>,
<code>#[syn([`braced`])]</code>,
<code>#[syn([`bracketed`])]</code>:
  Corresponds to the isonymous macros in `syn`.
  Must be attached to [`struct@Paren`], [`struct@Brace`], and [`struct@Bracket`] fields, respectively.

<code>#[syn(in = [`struct@Ident`])]</code>:
  The field is read from inside the named delimiter pair.

<code>#[parse(fn([`ParseStream`]) -> [`syn::Result`]\<T>)]</code>:
  A function used to parse the field,
  often used with [`Punctuated::parse_terminated`]
  or [`Attribute::parse_outer`].

<code>#[to_tokens(fn(&mut [`TokenStream`], &T)]</code>:
  A function used to tokenize the field.
  Often used with [`TokenStreamExt::append_all`],
  though for type resolution reasons this needs to be indirected through a closure expression.

## Enums

```rust
#[derive(Clone, Debug, syn_derive::Parse, syn_derive::ToTokens)]
enum ExampleEnum {
	#[parse(peek = Token![struct])]
	Struct(ItemStruct),
	#[parse(peek = Token![enum])]
	Enum(ItemEnum),

	Other {
		path: Path,
		semi_token: Token![;],
	}
}
```

<code>#[parse(peek = [`Token`])]</code>:
  Checks whether the variant should be parsed.
  Even if multiple peeks succeed, only the first successful variant is attempted.

<code>#[parse(peek_func = fn([`ParseStream`]) -> [`bool`])]</code>:
  More powerful than `peek` (such as allowing [`peek2`](syn::parse::ParseBuffer::peek2)), but gives worse error messages on failure.
  `peek` should be preferred when possible.

# Alternatives
- [`derive-syn-parse`](https://docs.rs/derive-syn-parse/latest/)
  does not handle [`ToTokens`].
  It also seems to encourage throwing tokens away with its `prefix` and `postfix` attributes.
- [`parsel`](https://docs.rs/derive-syn-parse/latest/)
  uses its own types for parentheses, meaning the AST types have different API from [`syn`]'s own.
