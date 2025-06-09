use std::{path::Path, process::Command};

use cool::codegen::Target;

fn compile_target(target: Target) {
    let cargo = env!("CARGO");

    let manifest = Path::new(env!("CARGO_MANIFEST_PATH"));
    let root = manifest
        .parent()
        .and_then(|p| p.parent())
        .unwrap()
        .to_str()
        .unwrap();

    let target_dir = format!("{root}/target/_coolc/runtime/rt-{target}");

    let out = Command::new(cargo)
        .arg("build")
        .arg("--release")
        .arg("--package")
        .arg("runtime")
        .arg("--target-dir")
        .arg(&target_dir)
        .arg("--target")
        .arg(target.triple())
        .output()
        .expect("failed to run cargo");
    if !out.status.success() {
        let error = String::from_utf8_lossy(&out.stderr);
        panic!("failed to build {target}:\n{error}");
    }

    // Cargo creates a folder with the target inside the path specified in
    // `--target-dir`. Hence `{target}` appears two times in the path.
    let cargo_triple = target.triple();
    let runtime_archive_path = format!("{target_dir}/{cargo_triple}/release/libruntime.a");
    println!("cargo::rustc-env=COOL_RT_{target}={runtime_archive_path}");
}

fn main() {
    println!("cargo::rerun-if-changed=../runtime");
    for target in Target::ALL {
        compile_target(*target);
    }
}
