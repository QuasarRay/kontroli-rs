use crate::{Command, Error, Opt, Stage};
use kontroli::error::Error as KoError;
use kontroli::kernel::{self, GCtx};
use rayon::iter::{ParallelBridge, ParallelIterator};

type Checks<'s> = (Vec<kernel::Check<'s>>, GCtx<'s>);

fn infer_with<'s, F>(cmd: Command<'s>, gc: &mut GCtx<'s>, mut f: F) -> Result<(), KoError>
where
    F: FnMut(kernel::Check<'s>, &GCtx<'s>) -> Result<(), KoError>,
{
    match cmd {
        Command::Intro(sym, it) => {
            let rewritable = it.rewritable();

            // defer checking to later
            let (typing, check) = kernel::intro(it, gc)?;
            if let Some(check) = check {
                f(check, gc)?
            }
            gc.insert(sym, typing, rewritable)?;
        }
        Command::Rules(rules) => {
            for rule in rules.iter().cloned() {
                let rule = rule.map_lhs(kontroli::Pattern::from);
                let rule = kontroli::Rule::try_from(rule).map_err(KoError::from)?;
                f(kernel::rewrite(rule, gc)?, gc)?;
            }
            rules.into_iter().try_for_each(|r| gc.add_rule(r))?
        }
    }
    Ok(())
}

fn infer_check<'s>(cmd: Command<'s>, opt: &Opt, gc: &mut GCtx<'s>) -> Result<(), KoError> {
    infer_with(cmd, gc, |check, gc| {
        if !opt.omits(Stage::Check) {
            check.check(gc)?
        };
        Ok(())
    })
}

fn infer<'s>(cmd: Command<'s>, gc: &mut GCtx<'s>) -> Result<Checks<'s>, KoError> {
    let mut checks = (Vec::new(), gc.clone());
    infer_with(cmd, gc, |check, _gc| {
        checks.0.push(check);
        Ok(())
    })?;
    Ok(checks)
}

fn check((checks, gc): Checks) -> Result<(), KoError> {
    checks.into_iter().try_for_each(|chk| Ok(chk.check(&gc)?))
}

/// Process a stream of commands.
pub fn infer_checks<'s, I>(iter: I, opt: &Opt, gc: &mut GCtx<'s>) -> Result<(), Error>
where
    I: Iterator<Item = Result<Command<'s>, Error>> + Send,
{
    let mut iter = iter.filter(|cmd| !opt.omits(Stage::Infer) || cmd.is_err());
    if opt.jobs.is_some() {
        iter.map(|cmd| infer(cmd?, gc).map_err(Error::Ko))
            .filter(|cmd| !opt.omits(Stage::Check) || cmd.is_err())
            .par_bridge()
            .try_for_each(|ts| check(ts?).map_err(Error::Ko))
    } else {
        iter.try_for_each(|cmd| infer_check(cmd?, opt, gc).map_err(Error::Ko))
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use kontroli::symbol::Owned;
    use kontroli::{App, LTerm, Pattern, Rule, RuleError, Symbol};

    #[test]
    fn unannotated_rewrite_rule_is_rejected_before_insertion() {
        let owned = Owned::new("f".to_string());
        let symbol = Symbol::new(&owned);
        let rule = Rule {
            ctx: vec![("X".to_string(), None)],
            lhs: App {
                symbol,
                args: vec![Pattern::MVar(0)],
            },
            rhs: LTerm::Var(0),
        };
        let mut gc = GCtx::new();

        let result = infer_with(Command::Rules(vec![rule]), &mut gc, |_check, _gc| Ok(()));

        assert!(matches!(
            result,
            Err(KoError::Rule(RuleError::TypeAnnotation))
        ));
    }
}
