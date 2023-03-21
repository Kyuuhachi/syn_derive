#![feature(proc_macro_diagnostic)]

/*!
A simple crate for reducing the boilerplate when writing parsers with [`syn`].

## Structs

```rust
# use syn::{*, token::Paren, punctuated::*};
# use quote::TokenStreamExt;
#[derive(syn_derive::Parse, syn_derive::ToTokens)]
struct ExampleStruct {
    #[parse(Attribute::parse_outer)]
    #[to_tokens(|tokens, val| tokens.append_all(val))]
    attrs: Vec<Attribute>,

    path: Path,

    #[syn(parenthesized)]
    paren_token: Paren,

    #[syn(in = paren_token)]
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
# use syn::{*, token::Paren, punctuated::*};
#[derive(syn_derive::Parse, syn_derive::ToTokens)]
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

<code>#[parse(prefix = fn([`ParseStream`]) -> [`syn::Result`]<_>)]</code>>:
  A prefix used for all branches, before doing the peeking.
  Useful when all branches support attributes, for example.
  The return value is ignored, which gives somewhat suboptimal performance, since the prefix is parsed twice.

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

*/

use proc_macro2::{Span, TokenStream};
use syn::parse::ParseStream;
use syn::{Token, parse_macro_input, Data, DeriveInput, Ident};
use syn::spanned::Spanned;
use proc_macro::{Diagnostic, Level};

#[proc_macro_derive(Parse, attributes(syn, parse))]
pub fn derive_parse(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input = parse_macro_input!(item as DeriveInput);
	derive_parse_inner(input).into()
}

#[proc_macro_derive(ToTokens, attributes(syn, to_tokens))]
pub fn derive_tokens(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input = parse_macro_input!(item as DeriveInput);
	derive_tokens_inner(input).into()
}

macro_rules! q {
	(_      => $($b:tt)*) => { ::quote::quote!         {                $($b)* } };
	($a:expr=> $($b:tt)*) => { ::quote::quote_spanned! { ($a).span() => $($b)* } };
}

macro_rules! pq {
	(_      => $($b:tt)*) => { ::syn::parse_quote!         {                $($b)* } };
	($a:expr=> $($b:tt)*) => { ::syn::parse_quote_spanned! { ($a).span() => $($b)* } };
}

trait Emit {
	type T;
	fn emit(self) -> Self::T;
}
impl Emit for syn::Error {
	type T = ();
	fn emit(self) {
		self.span().error(&self.to_string()).emit();
	}
}
impl<T> Emit for Result<T, syn::Error> {
	type T = Option<T>;
	fn emit(self) -> Option<T> {
		match self {
			Ok(v) => Some(v),
			Err(e) => { e.emit(); None }
		}
	}
}

trait SpanError: Spanned {
	fn warning(&self, text: &str) -> Diagnostic {
		Diagnostic:: spanned(self.span().unwrap(), Level::Warning, text)
	}

	fn error(&self, text: &str) -> Diagnostic {
		Diagnostic:: spanned(self.span().unwrap(), Level::Error, text)
	}
}
impl <T: Spanned> SpanError for T {}

fn derive_parse_inner(input: DeriveInput) -> TokenStream {
	let body = match input.data {
		Data::Struct(data) => {
			derive_parse_fields(pq!{_=> Self }, &data.fields)
		}
		Data::Enum(data) => {
			let mut prefix_expr = None::<syn::Expr>;
			for attr in &input.attrs {
				if attr.path().is_ident("parse") {
					attr.parse_nested_meta(|meta| {
						if meta.path.is_ident("prefix") {
							prefix_expr = Some(meta.value()?.parse()?);
							return Ok(());
						}
						Err(meta.error("unrecognized key"))
					}).emit();
				}
			}

			let mut main_body = TokenStream::new();
			for variant in data.variants {
				enum Peek {
					Token(syn::Expr),
					Func(syn::Expr),
				}

				let mut peek_expr = None::<Peek>;
				for attr in &input.attrs {
					if attr.path().is_ident("parse") {
						attr.parse_nested_meta(|meta| {
							if meta.path.is_ident("peek") {
								peek_expr = Some(Peek::Token(meta.value()?.parse::<syn::Expr>()?));
								return Ok(());
							}
							if meta.path.is_ident("peek_func") {
								peek_expr = Some(Peek::Func(meta.value()?.parse::<syn::Expr>()?));
								return Ok(());
							}
							Err(meta.error("unrecognized key"))
						}).emit();
					}
				}

				let ident = &variant.ident;
				let body = derive_parse_fields(pq!{ident=> Self::#ident }, &variant.fields);
				main_body.extend(match peek_expr {
					Some(Peek::Token(token)) => {
						q!{variant=>
							if __lookahead.peek(#token) { return #body; }
						}
					},
					Some(Peek::Func(func)) => {
						q!{variant=>
							let peek: fn(::syn::parse::ParseStream) -> bool = #func;
							if peek(&head.fork()) { return #body; }
						}
					},
					None => {
						q!{variant=> return #body; }
					},
				})
			}
			let prefix_expr = prefix_expr.iter();
			q!{_=> {
				let head = __input.fork();
				#( head.call(#prefix_expr)?; )*
				let __lookahead = head.lookahead1();
				#main_body
				#[allow(unreachable_code)]
				return Err(__lookahead.error())
			} }
		},
		Data::Union(_) => {
			Span::call_site().error("unions not supported").emit();
			q!{_=> { } }
		}
	};

	let name = &input.ident;
	let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
	q!{_=>
		#[automatically_derived]
		impl #impl_generics ::syn::parse::Parse for #name #ty_generics #where_clause {
			fn parse(__input: ::syn::parse::ParseStream) -> ::syn::Result<Self> #body
		}
	}
}

fn derive_tokens_inner(input: DeriveInput) -> TokenStream {
	let body = match input.data {
		Data::Struct(data) => {
			let (pat, body) = derive_tokens_fields(pq!{_=> Self }, &data.fields);
			q!{_=> let #pat = self; #body }
		}
		Data::Enum(data) => {
			let mut match_body = TokenStream::new();
			for variant in data.variants {
				let ident = &variant.ident;
				let (pat, body) = derive_tokens_fields(pq!{ident=> Self::#ident }, &variant.fields);
				match_body.extend(q!{variant=> #pat => #body, })
			}
			q!{_=> match self { #match_body } }
		},
		Data::Union(_) => {
			Span::call_site().error("unions not supported").emit();
			TokenStream::new()
		}
	};

	let name = &input.ident;
	let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
	q!{_=>
		#[automatically_derived]
		impl #impl_generics ::quote::ToTokens for #name #ty_generics #where_clause {
			fn to_tokens(&self, tokens: &mut ::proc_macro2::TokenStream) {
				#body
			}
		}
	}
}

fn derive_parse_fields(path: syn::Path, fields: &syn::Fields) -> TokenStream {
	let mut defs = TokenStream::new();
	let mut body = TokenStream::new();
	for (member, attr, field) in named(fields) {
		let stream = attr.stream.unwrap_or_else(|| pq!{_=> __input });

		let mut expr = None;
		for attr in &field.attrs {
			if attr.path().is_ident("parse") {
				expr = attr.parse_args::<syn::Expr>().emit()
					.map(|e| q!{e=> #stream.call(#e)?});
			}
		}

		let expr = match (expr, attr.delimiter) {
			(Some(expr), delimiter) => {
				if delimiter.is_some() {
					delimiter.span().error("cannot do custom parsing on delimiters").emit();
				}
				expr
			}
			(None, Some(delimiter)) => {
				defs.extend(q!{member=> let #member; });
				q!{member=> ::syn::#delimiter!(#member in #stream) }
			}
			(None, None) => {
				q!{member=> #stream.parse()? }
			}
		};
		body.extend(q!{member=> #member: #expr, });
	}
	q!{_=> { #defs ::syn::Result::Ok(#path { #body }) } }
}

fn derive_tokens_fields(path: syn::Path, fields: &syn::Fields) -> (TokenStream, TokenStream) {
	let mut pat = TokenStream::new();
	let mut body = TokenStream::new();
	let mut iter = named(fields).peekable();
	derive_tokens_fields_inner(&mut iter, None, &mut pat, &mut body);
	if let Some(a) = iter.next() {
		a.2.span().error("invalid `in`").emit();
	}
	(q!{_=> #path { #pat } }, q!{_=> { #body } })
}

fn derive_tokens_fields_inner(
	iter: &mut std::iter::Peekable<impl Iterator<Item = (syn::Member, FieldAttr, syn::Field)>>,
	stream: Option<Ident>,
	pat: &mut TokenStream,
	body: &mut TokenStream,
) {
	while let Some((member, attr, field)) = iter.next_if(|a| a.1.stream == stream) {
		let ident = match &member {
			syn::Member::Named(ident) => {
				pat.extend(q!{member=> #member, });
				ident.clone()
			}
			syn::Member::Unnamed(index) => {
				let i = index.index;
				let ident = quote::format_ident!("__{i}", span = index.span());
				pat.extend(q!{member=> #member: #ident, });
				ident
			}
		};

		let mut expr = None;
		for attr in &field.attrs {
			if attr.path().is_ident("to_tokens") {
				expr = attr.parse_args::<syn::Expr>().emit()
					.map(|e| q!{e=> {
						let __expr: fn(&mut ::proc_macro2::TokenStream, _) = #e;
						__expr(tokens, #ident)
					} });
			}
		}

		let expr = match (expr, attr.delimiter) {
			(Some(expr), delimiter) => {
				if delimiter.is_some() {
					delimiter.span().error("cannot do custom parsing on delimiters").emit();
				}
				expr
			}
			(None, Some(delimiter)) => {
				let mut body = TokenStream::new();
				derive_tokens_fields_inner(iter, Some(ident.clone()), pat, &mut body);
				q!{delimiter=> #ident.surround(tokens, |tokens| { #body }) }
			}
			(None, None) => q!{member=> #ident.to_tokens(tokens) },
		};

		body.extend(q!{field=> #expr; });
	}
}

#[derive(Clone, Debug, Default)]
struct FieldAttr {
	delimiter: Option<Ident>,
	stream: Option<Ident>,
}

fn parse_field_attr(attrs: &[syn::Attribute]) -> FieldAttr {
	mod kw {
		syn::custom_keyword!(parenthesized);
		syn::custom_keyword!(braced);
		syn::custom_keyword!(bracketed);
	}

	let result = get_attr(attrs, "syn")
		.map(|attr| attr.parse_args_with(|input: ParseStream| {
			let mut attr = FieldAttr::default();
			loop {
				if input.is_empty() {
					break
				}

				if input.peek(Token![in]) {
					let in_ = input.parse::<Token![in]>()?;
					if attr.stream.is_some() {
						in_.span().error("duplicate `in`").emit();
					}
					input.parse::<Token![=]>()?;
					attr.stream = Some(input.parse()?);
				} else if input.peek(kw::parenthesized) || input.peek(kw::braced) || input.peek(kw::bracketed) {
					let w = input.parse::<Ident>()?;
					if attr.delimiter.is_some() {
						w.span().error("duplicate delimiter").emit();
					}
					attr.delimiter = Some(w);
				} else {
					break
				}

				if !input.is_empty() {
					input.parse::<Token![,]>()?;
				}
			}

			if !input.is_empty() {
				input.span().error("unexpected token").emit();
				input.parse::<TokenStream>().unwrap();
			}
			Ok(attr)
		})).transpose();

	match result {
		Ok(a) => a.unwrap_or_default(),
		Err(e) => {
			e.span().error(&e.to_string()).emit();
			FieldAttr::default()
		},
	}
}

fn named(
	fields: &syn::Fields
) -> impl Iterator<Item=(syn::Member, FieldAttr, syn::Field)> + '_ {
	fields.iter().cloned()
		.enumerate()
		.map(|(i, f)| (
			f.ident.clone().map_or_else(
				|| syn::Member::Unnamed(syn::Index { index: i as u32, span: f.span() }),
				syn::Member::Named,
			),
			parse_field_attr(&f.attrs),
			f,
		))
}

fn get_attr<'a>(attrs: &'a [syn::Attribute], name: &str) -> Option<&'a syn::Attribute> {
	let mut iter = attrs.iter()
		.filter(|a| a.path().is_ident(name));
	let a = iter.next();
	if let Some(b) = iter.next() {
		b.path().span().error("duplicate attribute").emit();
	}
	a
}
