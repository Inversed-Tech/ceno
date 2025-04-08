use ff_ext::GoldilocksExt2;
use itertools::Itertools;
use mpcs::{
    Basefold, BasefoldRSParams, PolynomialCommitmentScheme,
    test_util::{get_point_from_challenge, setup_pcs},
};

use multilinear_extensions::{mle::MultilinearExtension, virtual_poly::ArcMultilinearExtension};
use rand::rngs::OsRng;
use transcript::BasicTranscript;
use witness::RowMajorMatrix;

use clap::Parser;
use tracing_profile::init_tracing;

type Pcs = Basefold<GoldilocksExt2, BasefoldRSParams>;
type T = BasicTranscript<GoldilocksExt2>;
type E = GoldilocksExt2;

#[derive(Parser, Debug)]
struct Args {
    #[arg(short = 'd', long, default_value = "20")]
    num_variables: usize,
    #[arg(short = 'b', long, default_value = "6")]
    batch_size: usize,
}

fn main() {
    let _guard = init_tracing().expect("failed to initialize tracing");
    let args = Args::parse();
    let num_vars = args.num_variables;
    let batch_size = args.batch_size;

    let (pp, _vp) = setup_pcs::<E, Pcs>(num_vars);
    let mut transcript = T::new(b"BaseFold");
    let rmm = RowMajorMatrix::rand(&mut OsRng, 1 << num_vars, batch_size);
    let polys = rmm.to_mles();
    let comm = Pcs::batch_commit_and_write(&pp, rmm, &mut transcript).unwrap();

    let point = get_point_from_challenge(num_vars, &mut transcript);
    let evals = polys.iter().map(|poly| poly.evaluate(&point)).collect_vec();

    let polys = polys
        .iter()
        .map(|poly| ArcMultilinearExtension::from(poly.clone()))
        .collect::<Vec<_>>();
    let _proof =
        Pcs::simple_batch_open(&pp, &polys, &comm, &point, &evals, &mut transcript).unwrap();
}
