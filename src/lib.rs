#![feature(trait_upcasting)]
use std::fmt;

use pod2::middleware::TypedValue;

pub mod ecdsapod;
pub mod ed25519pod;
pub(crate) mod gadgets;
pub mod mdlpod;
pub mod rsapod;

pub enum PodType {
    Ecdsa = 1001,
    Ed25519 = 1002,
    Rsa = 1003,
    Mdl = 1004,
}

impl fmt::Display for PodType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PodType::Ecdsa => write!(f, "Ecdsa"),
            PodType::Mdl => write!(f, "Mdl"),
            PodType::Ed25519 => write!(f, "Ed25519"),
            PodType::Rsa => write!(f, "Rsa"),
        }
    }
}
impl From<PodType> for TypedValue {
    fn from(t: PodType) -> Self {
        TypedValue::from(t as i64)
    }
}

#[cfg(test)]
pub mod tests {
    use std::any::Any;

    use plonky2::hash::hash_types::HashOut;
    use pod2::{
        self,
        backends::plonky2::{Result, mainpod},
        frontend::MainPodBuilder,
        middleware::{F, Params, Pod, RawValue, RecursivePod, VDSet, Value},
        op, timed,
    };

    /// abstracted test to check Introduction PODs that are about proving
    /// knowledge of a private key through verifying a signature.
    pub(crate) fn test_introduction_pod_signature_flow(
        intro_pod: Box<dyn RecursivePod>,
        params: Params,
        vd_set: VDSet,
        key_signed_msg: &str,
        msg_hash: HashOut<F>,
    ) -> Result<()> {
        intro_pod.verify().unwrap();

        // wrap the intro_pod in a 'MainPod' (RecursivePod)
        let main_ecdsa_pod = pod2::frontend::MainPod {
            pod: intro_pod.clone(),
            public_statements: intro_pod.pub_statements(),
            params: params.clone(),
        };

        // now generate a new MainPod from the intro_pod
        let mut main_pod_builder = MainPodBuilder::new(&params, &vd_set);
        main_pod_builder.add_recursive_pod(main_ecdsa_pod.clone());

        // add operation that ensures that the msg is as expected in the EcdsaPod
        let msg_copy = main_pod_builder
            .pub_op(op!(
                new_entry,
                key_signed_msg,
                Value::from(RawValue(msg_hash.elements))
            ))
            .unwrap();
        main_pod_builder
            .pub_op(op!(eq, (&main_ecdsa_pod, key_signed_msg), msg_copy))
            .unwrap();

        // perpetuate the pk
        main_pod_builder
            .pub_op(op!(copy, main_ecdsa_pod.public_statements[2].clone()))
            .unwrap();

        let mut prover = pod2::backends::plonky2::mock::mainpod::MockProver {};
        let pod = main_pod_builder.prove(&mut prover, &params).unwrap();
        assert!(pod.pod.verify().is_ok());

        println!("going to prove the main_pod");
        let mut prover = mainpod::Prover {};
        let main_pod = timed!(
            "main_pod_builder.prove",
            main_pod_builder.prove(&mut prover, &params).unwrap()
        );
        let pod = (main_pod.pod as Box<dyn Any>)
            .downcast::<mainpod::MainPod>()
            .unwrap();
        pod.verify().unwrap();

        Ok(())
    }
}
