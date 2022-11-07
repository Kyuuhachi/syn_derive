#![feature(proc_macro_diagnostic)]

#![doc = include_str!("../README.md")]

use proc_macro2::{Span, TokenStream};
use syn::parse::ParseStream;
use syn::{Token, parse_macro_input, Data, DeriveInput, Ident};
use syn::spanned::Spanned;
use proc_macro::{Diagnostic, Level};

#[cfg(doc)]
use {
	syn::token::{Paren, Brace, Bracket},
	syn::punctuated::Punctuated,
	syn::Attribute,
	quote::TokenStreamExt,
};

#[proc_macro_derive(Parse, attributes(syn, parse))]
pub fn derive_parse(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input = parse_macro_input!(item as DeriveInput);
	let a = derive_parse_inner(input);
	println!("{a}");
	a.into()
}

#[proc_macro_derive(ToTokens, attributes(syn, to_tokens))]
pub fn derive_tokens(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let input = parse_macro_input!(item as DeriveInput);
	let a = derive_tokens_inner(input);
	println!("{a}");
	a.into()
}

macro_rules! q {
	(_      => $($b:tt)*) => { ::quote::quote!         {                $($b)* } };
	($a:expr=> $($b:tt)*) => { ::quote::quote_spanned! { ($a).span() => $($b)* } };
}

macro_rules! pq {
	(_      => $($b:tt)*) => { ::syn::parse_quote!         {                $($b)* } };
	($a:expr=> $($b:tt)*) => { ::syn::parse_quote_spanned! { ($a).span() => $($b)* } };
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
			let mut main_body = TokenStream::new();
			for variant in data.variants {
				let peek_expr = get_attr(&variant.attrs, "parse")
					.map(|attr| attr.parse_args_with(|input: ParseStream| {
						mod kw {
							syn::custom_keyword!(peek);
						}
						input.parse::<kw::peek>()?;
						input.parse::<Token![=]>()?;
						input.parse::<syn::Expr>()
					})).transpose();
				let peek_expr = match peek_expr {
					Ok(a) => a,
					Err(e) => {
						e.span().error(&e.to_string()).emit();
						None
					},
				};

				let ident = &variant.ident;
				let body = derive_parse_fields(pq!{ident=> Self::#ident }, &variant.fields);
				if let Some(expr) = peek_expr {
					main_body.extend(q!{variant=>
						let peek: fn(ParseStream) -> bool = #expr;
						if peek(__input) { return #body; }
					})
				} else {
					main_body.extend(q!{variant=> return #body; })
				}
			}
			pq!{_=> { #main_body } }
		},
		Data::Union(_) => {
			Span::call_site().error("unions not supported").emit();
			pq!{_=> { } }
		}
	};

	let name = &input.ident;
	let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
	q!{_=>
		#[automatically_derived]
		impl #impl_generics ::syn::parse::Parse for #name #ty_generics #where_clause {
			fn parse(__input: ::syn::parse::ParseStream) -> ::syn::Result<Self> {
				#body
			}
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

fn derive_parse_fields(path: syn::Path, fields: &syn::Fields) -> syn::Block {
	let mut defs = TokenStream::new();
	let mut body = TokenStream::new();
	for (member, attr, field) in named(fields) {
		let stream = attr.stream.unwrap_or_else(|| pq!{_=> __input });

		let parse_expr = get_attr(&field.attrs, "parse").map(|attr| match attr.parse_args::<syn::Expr>() {
			Ok(expr) => {
				q!{expr=> #stream.call(#expr)? }
			}
			Err(e) => {
				e.span().error(&e.to_string()).emit();
				q!{ e=> panic!() }
			}
		});

		let parse_expr = if let Some(delimiter) = attr.delimiter {
			if parse_expr.is_some() {
				delimiter.span().error("cannot do custom parsing on delimiters").emit();
			}
			defs.extend(q!{member=> let #member; });
			q!{member=> syn::#delimiter!(#member in #stream) }
		} else {
			parse_expr.unwrap_or_else(|| q!{member=> #stream.parse()? } )
		};
		body.extend(q!{member=> #member: #parse_expr, });
	}
	pq!{_=> { #defs ::syn::Result::Ok(#path { #body }) } }
}

fn derive_tokens_fields(path: syn::Path, fields: &syn::Fields) -> (syn::Pat, syn::Block) {
	let mut pat = TokenStream::new();
	let mut body = TokenStream::new();
	let mut iter = named(fields).peekable();
	derive_tokens_fields_inner(&mut iter, None, &mut pat, &mut body);
	if let Some(a) = iter.next() {
		a.2.span().error("invalid `in`").emit();
	}
	(pq!{_=> #path { #pat } }, pq!{_=> { #body } })
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
			},
			syn::Member::Unnamed(index) => {
				let i = index.index;
				let ident = quote::format_ident!("__{i}", span = index.span());
				pat.extend(q!{member=> #member: #ident, });
				ident
			},
		};

		let tokens_expr = get_attr(&field.attrs, "to_tokens")
			.map(|attr| match attr.parse_args::<syn::Expr>() {
				Ok(expr) => {
					let ty = &field.ty;
					q!{expr=> {
						let __expr: fn(&mut TokenStream, &#ty) = #expr;
						__expr(tokens, #ident)
					} }
				}
				Err(e) => {
					e.span().error(&e.to_string()).emit();
					q!{e=> panic!() }
				}
			});

		let tokens_expr = if let Some(delimiter) = attr.delimiter {
			if tokens_expr.is_some() {
				delimiter.span().error("cannot do custom parsing on delimiters").emit();
			}
			let mut body = TokenStream::new();
			derive_tokens_fields_inner(iter, Some(ident.clone()), pat, &mut body);
			q!{delimiter=> #ident.surround(tokens, |tokens| { #body }) }
		} else {
			tokens_expr.unwrap_or_else(|| q!{member=> #ident.to_tokens(tokens) })
		};

		body.extend(q!{field=> #tokens_expr; });
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
		.filter(|a| a.path.is_ident(name));
	let a = iter.next();
	if let Some(b) = iter.next() {
		b.path.span().error("duplicate attribute").emit();
	}
	a
}

