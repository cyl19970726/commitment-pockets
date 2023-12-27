mod error;

use std::ops::BitAnd;
use std::ptr::null;
use ark_ec::CurveGroup;
use std::u64;

use error::PocketError;

mod poly;
pub use poly::{EvaluationDomain, UniPolynomial};

mod basic;
pub use basic::{BasicParameters, BasicPolyCommit, BasicProof};

mod basic_ped;
pub use basic_ped::{BasicPEDParameters, BasicPEDPolyCommit, BasicPEDProof};

mod multiproof;
pub use multiproof::{
    MultiProof, MultiProofParameters, MultiProofPolyCommit, MultiProofPolyCommit2,
};

use ark_ff::{BigInt, BigInteger, BigInteger128, BigInteger320, BigInteger64, CyclotomicMultSubgroup, Field, One, PrimeField};

mod asvc;
pub use asvc::{ASvccommit, ASvckey, ASvcproof};

mod caulk_single;
pub use caulk_single::{CaulkParameters, CaulkSinglePolyCommit, CaulkSingleProof, PedersenProof};

use ark_ec::pairing::Pairing;
use ark_std::{ops::Add, ops::Mul, Zero};

pub fn multiexp<E: Pairing>(
    bases: &Vec<E::G1Affine>,
    exponents: Vec<E::ScalarField>,
) -> Result<E::G1Affine, PocketError> {
    //TODO: it is a native version, and it will be improved.
    let mut acc = E::G1::zero().into();
    for (e, b) in exponents.iter().zip(bases.iter()) {
        acc = acc.add(&b.mul(e)).into();
    }
    Ok(acc)
}

pub fn multiexp2<E: Pairing>(
    bases: &Vec<E::G2Affine>,
    exponents: Vec<E::ScalarField>,
) -> Result<E::G2Affine, PocketError> {
    //TODO: it is a native version, and it will be improved.
    let mut acc = E::G2::zero().into();
    for (e, b) in exponents.iter().zip(bases.iter()) {
        acc = acc.add(&b.mul(e)).into();
    }
    Ok(acc)
}

const N_BIT: usize = 2;
pub fn pippenger<E: Pairing>(
    bases: &Vec<E::G1Affine>,
    exponents: Vec<E::ScalarField>,
) -> Result<E::G1Affine, PocketError> {
    // ) -> Result<E::G1Affine, PocketError> {
    let modulus_bit_size = E::BaseField::MODULUS_BIT_SIZE;
    // G = k0 * P0 + k1 * P1 + ... + k_i * P_i
    // we can split each element of exponents into k = k_0 *2^0 ... k_j * 2^cj
    // which k \in [0, 2^c) is the window size and the j is the window index

    // G = k0 * p0 + k1 * p1
    // i row j column
    // k_0,0 k_0,1 k_0,2 ==> n_ki[0]
    // k_1,0 k_1,1 k_1,2 ==> n_ki[1]
    let n_ki: Vec<Vec<u32>> = exponents
        .into_iter()
        .map(|v| split_to_nbit_uint_form::<E::ScalarField>(v, N_BIT))
        .collect::<Vec<Vec<u32>>>();

    // Split the vector into n_ki
    // Calculate S_i Set
    // collect all the k_j with the same window_index 'j' from different 'k_i' into one vector
    let mut window_index_set_vec: Vec<Vec<u32>> = Vec::new();
    let mut split_nums = n_ki[0].len();
    // check the k_i numbers
    n_ki.clone().into_iter().for_each(|vec|{
        if vec.len() != split_nums{
            panic!("err k_i numbers")
        }
    });

    for i in 0..split_nums{
        window_index_set_vec.push(Vec::new());
    }

    // k_0,0 k_1,0 window_index_set_vec[0]
    // k_0,1 k_1,1 window_index_set_vec[1]
    // k_0,2 k_1,2 window_index_set_vec[2]
    n_ki.into_iter().for_each(|value| {
        for j in 0..split_nums {
            window_index_set_vec[j].push(value[j]);
        }
    });

    // Calculate the each S_i set different numbers of Pi
    // NOTICE: we no need to record the 0 number element
    let result_g =
        window_index_set_vec
            .into_iter()
            .enumerate()
            .fold(E::G1::zero(), |acc_B, (j, value)| {
                // change to array
                // let mut lamada_to_P = Vec::with_capacity(2^N_BIT);
                let mut lamada_to_P: [Vec<usize>; 2_usize.pow(N_BIT as u32)] = std::array::from_fn(|_| Vec::new());

                value.into_iter().enumerate().for_each(
                    // lamada express the coefficient for each P_i
                    |(i,lamada)| {
                        lamada_to_P[lamada as usize].push(i);
                    },
                );

                // Calculate T Set
                let mut T: [E::G1Affine;2_usize.pow(N_BIT as u32)] = std::array::from_fn(|_| E::G1::zero().into());
                for index in 0..lamada_to_P.len() {
                    let s_index = lamada_to_P.len() - 1 - index;
                    T[index] = lamada_to_P[s_index]
                        .iter()
                        .fold(E::G1::zero().into(), |acc, P_index| {
                            acc.add(bases[*P_index]).into()
                        });
                    if index != 0 {
                        T[index] = T[index - 1];
                    }
                }

                // Calculate the summation of T
                let B_j = T
                    .into_iter()
                    .enumerate()
                    .fold(E::G1::zero(), |acc, (lamada, acc_value)| {
                        acc_value.mul(E::ScalarField::from(lamada as u128))
                    });

                let mut powers =  <<E as Pairing>::ScalarField as PrimeField>::BigInt::from(1_u64);
                powers.muln(N_BIT as u32 * j as u32);
                acc_B + B_j.mul(E::ScalarField::from_bigint(powers).unwrap())
            });

    Ok(result_g.into_affine())
}

trait FromBits {
    fn from_bits_le(value: &[bool]) -> Self;

    fn to_bits_le(value: Self) ->  Vec<bool>;
}

impl FromBits for u32 {
    //transform the bits representation into value representation
    fn from_bits_le(value: &[bool]) -> Self {
        value.into_iter().enumerate().fold(0, |acc, item| {
            if *item.1 == true {
                let square = 2_u32.pow((item.0 as u32));
                let tmp = acc + square;
                tmp
            } else {
                acc
            }
        })
    }

    fn to_bits_le(value_in: u32) -> Vec<bool>{
        let mut temp = Vec::new();
        let mut value = value_in.clone();
        while  value !=0 {
            if value % 2 == 1 {
                temp.push(true);
            }else{
                temp.push(false);
            }
            value = value/2;
        }

       temp
    }
}

pub fn split_to_nbit_uint_form<F: PrimeField>(value: F, nbit: usize) -> Vec<u32> {
    let mut arr: Vec<bool> = value.into_bigint().to_bits_le();
    if arr.len() % nbit != 0 {
        for _ in 0..(nbit - arr.len() % nbit) {
            arr.push(false);
        }
    }
    // 4bit
    // 2bit
    // split index 0 2 4
    // 8bit
    // 2bit
    // split index 2 4 6
    let mut window_values: Vec<u32> = Vec::new();
    println!("arr_len {}",arr.len());
    for index in 0..(arr.len() / nbit) {
        let mut t_arr = arr.clone();
        let window_bits: &[bool] = &t_arr.as_mut_slice()[index * nbit..(index + 1) * nbit];
        let window_value = u32::from_bits_le(window_bits);
        window_values.push(window_value);
    }
    window_values
}

/// example
/// we want to split 30 whose binary form is 011111 to 2-bit form, we need to follow the below steps
/// 1) if 30 % 4 = 2                            [2]
/// 2) 30 divided by 2^2 will equal 7,
/// 3) if 7 % 4 = 3                             [2,3]
/// 4) 7 divided by 2^2 will equal 1,
/// 5) 1 % 4 = 1                                [2,3,1]
/// 6) 1 divided by 2^2 will equal 0 , break
///
/// 011110
/// 2 * 2^0 + 3 * 2^2 + 1 * 2^4 = 30
pub fn split_to_nbit_form<F: PrimeField>(value: F, nbit: usize) -> Vec<BigInt<2>> {
    let mut arr: Vec<bool> = value.into_bigint().to_bits_le();
    if arr.len() % nbit != 0 {
        for _ in 0..(nbit - arr.len() % nbit) {
            arr.push(false);
        }
    }
    // 4bit
    // 2bit
    // split index 0 2 4
    // 8bit
    // 2bit
    // split index 2 4 6
    let mut window_values: Vec<BigInt<2>> = Vec::new();
    for index in 0..(arr.len() / nbit) {
        let mut t_arr = arr.clone();
        let window_bits: &[bool] = &t_arr.as_mut_slice()[index * nbit..(index + 1) * nbit];
        let window_value: BigInteger128 = BigInteger::from_bits_le(window_bits);
        window_values.push(window_value);
    }
    window_values
}

pub fn Combine_nbit_form<F: PrimeField>(window_values: Vec<u32>, nbit: usize) -> F {
    let mut res:Vec<BigInt<2>> = Vec::new();
    window_values.into_iter().for_each(|v| {
         res.push(BigInteger128::from(v))
    });
    combine_nbit_form(res,nbit)
}

pub fn combine_nbit_form<F: PrimeField>(window_values: Vec<BigInt<2>>, nbit: usize) -> F {
    let mut arr: Vec<bool> = Vec::new();
    for window_value in window_values {
        let mut window_bits: Vec<bool> = window_value.to_bits_le();
        if window_bits.len() < nbit {
            for _ in 0..(nbit - window_bits.len()) {
                window_bits.push(false);
            }
        }
        arr.append(&mut window_bits);
    }
    F::from_bigint(BigInteger::from_bits_le(&arr)).unwrap()
}

mod tests{
    use super::*;
    use basic::*;
    use ark_bls12_381::Bls12_381;
    use ark_bls12_381::Fr;
    use rand::thread_rng;
    use ark_ff::UniformRand;
    use ark_ec::pairing::Pairing;
    use ark_ec::bls12::Bls12;

    #[test]
    fn test_split_and_combine_u32(){
        // binary representation
        // 1000
        // little
        // 0001
        let a: u32 = 8;
        let bits = u32::to_bits_le(a);
        println!("{} {} {} {}",bits[0],bits[1],bits[2],bits[3]);
        // [0,0,0,1]
        assert_eq!(bits[3],true);
        let recover = u32::from_bits_le(bits.as_slice());
        assert_eq!(recover,a);

        let a: u32 = 11;
        let bits = u32::to_bits_le(a);
        println!("{} {} {} {}",bits[0],bits[1],bits[2],bits[3]);
        // [0,0,0,1]
        assert_eq!(bits[3],true);
        let recover = u32::from_bits_le(bits.as_slice());
        assert_eq!(recover,a);
    }

    #[test]
    fn test_split_and_combine_PrimeField() {

        // let a = Fr::rand(&mut rng);
        let rng: &mut rand::rngs::ThreadRng = &mut thread_rng();
        let a = Fr::rand(rng);

        // We can access the prime modulus associated with `F`:
        // let modulus = <Fr as PrimeField>::MODULUS;
        // assert_eq!(a.pow(&modulus), a); // the Euler-Fermat theorem tells us: a^{p-1} = 1 mod p

        let windows = split_to_nbit_uint_form(a, N_BIT);
        println!("{} {} {} {} len:{}",windows[0],windows[1],windows[2],windows[3],windows.len());

        let res: Fr  = Combine_nbit_form(windows,N_BIT);

        let e = res.eq(&a);
        assert_eq!(e,true);

    }

    #[test]
    fn test_pippenger(){

        let rng: &mut rand::rngs::ThreadRng = &mut thread_rng();
        let poly_degree = 32;
        let params = BasicParameters::<Bls12_381>::new(poly_degree +2, rng).unwrap();

        // let poly = UniPolynomial::<Bls12_381>::new(vec![
        //     Fr::rand(rng),
        //     Fr::rand(rng),
        //     Fr::rand(rng),
        //     Fr::rand(rng),
        //     Fr::rand(rng),
        //     Fr::rand(rng),
        //     Fr::rand(rng),
        //     Fr::rand(rng),
        //     Fr::rand(rng),
        // ]);

        let poly = UniPolynomial::<Bls12_381>::new(vec![
            Fr::from(1),
            Fr::from(63),
            Fr::from(4),
            Fr::from(1),
        ]);
        let poly_vec1 = poly.clone().deref().to_vec();
        let poly_vec2 = poly.clone().deref().to_vec();

        let v1= multiexp::<Bls12_381>(&params.clone().g1_vec(poly_degree + 2).unwrap(),poly_vec1).unwrap();
        let v2= pippenger::<Bls12_381>(&params.g1_vec(poly_degree + 2).unwrap(),poly_vec2).unwrap();
        assert_eq!(v1,v2);


    }

}