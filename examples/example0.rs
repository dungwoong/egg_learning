use egg::{*, rewrite as rw};
// rewrite is a macro. You call it with rewrite!, but we import as rw
// found in macros.rs


fn main() {
    // Define a simple language
    define_language! {
        enum Simple {
            Num(i32),
            "+" = Add([Id; 2]),
            "*" = Mul([Id; 2]),
            Symbol(Symbol),
        }
    }

    // Make a runner
    let runner: Runner<Simple, ()> = Runner::default()
        .with_expr(&"(+ 0 (* 1 x))".parse().unwrap())
        .run(&[
            rw!("comm-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
            rw!("mul-1"; "(* 1 ?a)" => "?a"),
            rw!("add-0"; "(+ 0 ?a)" => "?a"),
        ]);

    // Extract the best expression
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);

    println!("Best expression with cost {best_cost}: {best_expr}");
}
