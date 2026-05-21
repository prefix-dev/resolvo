use super::{ConditionalSpec, Pack, Spec, SpecCondition};
use chumsky::{
    IterParser, Parser, error,
    error::LabelError,
    extra,
    extra::ParserExtra,
    input::{SliceInput, StrInput},
    pratt::{infix, left},
    prelude::{any, just},
    text,
    text::{Char, TextExpected},
    util::MaybeRef,
};
use resolvo::LogicalOperator;
use version_ranges::Ranges;

/// Parses a package name identifier.
pub fn name<'src, I, E>() -> impl Parser<'src, I, <I as SliceInput<'src>>::Slice, E> + Copy
where
    I: StrInput<'src>,
    I::Token: Char + 'src,
    E: ParserExtra<'src, I>,
    E::Error: LabelError<'src, I, TextExpected<'src, I>>,
{
    any()
        .try_map(|c: I::Token, span| {
            if c.to_ascii()
                .map(|i| i.is_ascii_alphabetic() || i == b'_')
                .unwrap_or(false)
            {
                Ok(c)
            } else {
                Err(LabelError::expected_found(
                    [TextExpected::IdentifierPart],
                    Some(MaybeRef::Val(c)),
                    span,
                ))
            }
        })
        .then(
            any()
                .try_map(|c: I::Token, span| {
                    if c.to_ascii()
                        .is_some_and(|i| i.is_ascii_alphanumeric() || i == b'_' || i == b'-')
                    {
                        Ok(())
                    } else {
                        Err(LabelError::expected_found(
                            [TextExpected::IdentifierPart],
                            Some(MaybeRef::Val(c)),
                            span,
                        ))
                    }
                })
                .repeated(),
        )
        .to_slice()
}

/// Parses a range of package versions. E.g. `5` or `1..5`.
fn ranges<'src>()
-> impl Parser<'src, &'src str, Ranges<Pack>, extra::Err<error::Simple<'src, char>>> {
    text::int(10)
        .map(|s: &str| s.parse().unwrap())
        .then(
            just("..")
                .padded()
                .ignore_then(text::int(10).map(|s: &str| s.parse().unwrap()).padded())
                .or_not(),
        )
        .map(|(left, right)| {
            let right = Pack::new(right.unwrap_or_else(|| left + 1));
            Ranges::between(Pack::new(left), right)
        })
}

/// Parses a single [`Spec`]. E.g. `foo 1..2` or `bar 3` or `baz`.
pub(crate) fn spec<'src>()
-> impl Parser<'src, &'src str, Spec, extra::Err<error::Simple<'src, char>>> {
    name()
        .padded()
        .then(ranges().or_not())
        .map(|(name, range)| Spec::new(name.to_string(), range.unwrap_or(Ranges::full())))
}

fn condition<'src>()
-> impl Parser<'src, &'src str, SpecCondition, extra::Err<error::Simple<'src, char>>> {
    let and = just("and").padded().map(|_| LogicalOperator::And);
    let or = just("or").padded().map(|_| LogicalOperator::Or);

    let single = spec().map(SpecCondition::Requirement);

    single.pratt((
        infix(left(1), and, |lhs, op, rhs, _| {
            SpecCondition::Binary(op, Box::new([lhs, rhs]))
        }),
        infix(left(1), or, |lhs, op, rhs, _| {
            SpecCondition::Binary(op, Box::new([lhs, rhs]))
        }),
    ))
}

pub(crate) fn union_spec<'src>()
-> impl Parser<'src, &'src str, Vec<Spec>, extra::Err<error::Simple<'src, char>>> {
    spec()
        .separated_by(just("|").padded())
        .at_least(1)
        .collect()
}

pub(crate) fn conditional_spec<'src>()
-> impl Parser<'src, &'src str, ConditionalSpec, extra::Err<error::Simple<'src, char>>> {
    union_spec()
        .then(just("; if").padded().ignore_then(condition()).or_not())
        .map(|(spec, condition)| ConditionalSpec {
            condition,
            specs: spec,
        })
}
