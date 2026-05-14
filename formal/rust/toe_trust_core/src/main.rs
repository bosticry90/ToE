use serde::Deserialize;
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Debug, Deserialize)]
struct ArchitectureSchema {
    schema_id: String,
    schema_version: u64,
    pillar_required_phases: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct PillarMatrixRoot {
    pillars: serde_json::Value,
}

#[derive(Debug, Deserialize)]
struct PhaseRegistryRoot {
    registry_id: String,
    registry_version: u64,
    pillars: Vec<PhaseRegistryEntry>,
}

#[derive(Debug, Deserialize)]
struct PhaseRegistryEntry {
    pillar_id: String,
    mode: String,
}

fn find_repo_root(start: &Path) -> Result<PathBuf, String> {
    let mut p = start.to_path_buf();
    loop {
        if p.join("formal").exists() {
            return Ok(p);
        }
        if !p.pop() {
            return Err("Could not locate repo root (expected a 'formal' directory).".to_string());
        }
    }
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
    let text = fs::read_to_string(path)
        .map_err(|e| format!("Failed reading {}: {}", path.display(), e))?;
    serde_json::from_str::<T>(&text)
        .map_err(|e| format!("Failed parsing {}: {}", path.display(), e))
}

fn run() -> Result<(), String> {
    let cwd = std::env::current_dir().map_err(|e| format!("Could not resolve CWD: {e}"))?;
    let repo = find_repo_root(&cwd)?;

    let schema_path = repo.join("ARCHITECTURE_SCHEMA_v1.json");
    let matrix_path = repo.join("formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json");
    let phase_registry_path = repo.join("formal/docs/release/PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json");

    let schema: ArchitectureSchema = read_json(&schema_path)?;
    let matrix: PillarMatrixRoot = read_json(&matrix_path)?;
    let phase_registry: PhaseRegistryRoot = read_json(&phase_registry_path)?;

    if schema.schema_id != "ARCHITECTURE_SCHEMA_v3" {
        return Err(format!(
            "Unexpected schema_id '{}'; expected 'ARCHITECTURE_SCHEMA_v3'.",
            schema.schema_id
        ));
    }

    if schema.schema_version != 3 {
        return Err(format!(
            "Unexpected schema_version {}; expected 3.",
            schema.schema_version
        ));
    }

    if schema.pillar_required_phases.len() != 10 {
        return Err(format!(
            "pillar_required_phases length {} does not match expected 10.",
            schema.pillar_required_phases.len()
        ));
    }

    if phase_registry.registry_id != "PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0" {
        return Err(format!(
            "Unexpected registry_id '{}'; expected 'PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0'.",
            phase_registry.registry_id
        ));
    }

    if phase_registry.registry_version != 1 {
        return Err(format!(
            "Unexpected registry_version {}; expected 1.",
            phase_registry.registry_version
        ));
    }

    let Some(pillars_obj) = matrix.pillars.as_object() else {
        return Err("PILLAR_STATUS_MATRIX_v1.json must expose an object at key 'pillars'.".to_string());
    };

    if pillars_obj.is_empty() {
        return Err("PILLAR_STATUS_MATRIX_v1.json has no pillar rows under 'pillars'.".to_string());
    }

    if phase_registry.pillars.is_empty() {
        return Err("PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json has no pillar entries.".to_string());
    }

    let mut seen = HashSet::new();
    for row in &phase_registry.pillars {
        if row.pillar_id.trim().is_empty() {
            return Err("Phase registry contains an empty pillar_id entry.".to_string());
        }
        if row.mode.trim().is_empty() {
            return Err(format!(
                "Phase registry pillar '{}' has an empty mode token.",
                row.pillar_id
            ));
        }
        if !seen.insert(row.pillar_id.clone()) {
            return Err(format!("Duplicate phase registry pillar_id '{}'.", row.pillar_id));
        }
        if !pillars_obj.contains_key(&row.pillar_id) {
            return Err(format!(
                "Phase registry pillar '{}' is missing from matrix pillars.",
                row.pillar_id
            ));
        }
    }

    println!(
        "toe_trust_core: ok (schema_id={}, matrix_pillars={}, registry_pillars={})",
        schema.schema_id,
        pillars_obj.len(),
        phase_registry.pillars.len()
    );
    Ok(())
}

fn main() {
    if let Err(err) = run() {
        eprintln!("toe_trust_core: FAIL: {err}");
        std::process::exit(1);
    }
}
