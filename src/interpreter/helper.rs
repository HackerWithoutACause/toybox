use super::*;

pub trait ExternalFunction {
    fn types(&self) -> Vec<(Vec<Type>, Type)>;
    fn execute(&self, i: usize, args: Vec<Reference>, _dry: bool) -> Reference;
}

impl<F, R: Objectable> ExternalFunction for F
where
    F: Fn(bool) -> R,
{
    fn types(&self) -> Vec<(Vec<Type>, Type)> {
        vec![(vec![], R::typed())]
    }

    fn execute(&self, _i: usize, _args: Vec<Reference>, dry: bool) -> Reference {
        wrap(self(dry).objectify())
    }
}

// impl<F, A1: Objectable> ExternalFunction for F where F: Fn(A1) -> () {
//     fn types(&self) -> (Vec<Type>, Type) {
//         (vec![A1::typed()], Type::Nothing)
//     }

//     fn execute(&self, args: Vec<Reference>) -> Reference {
//         wrap(self(A1::convert(args[0].borrow().clone()).unwrap()).objectify())
//     }
// }
