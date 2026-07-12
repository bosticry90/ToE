import ToeFormal.Release.LoopControlRegistryShardingReadOnlyPrototypeExecutionPacketV2

/-
  Independent review certificate for the frozen registry Stage-A v2
  preparation.  The review reconstructs the schema graph and full custody
  scale, but rejects authorization because dynamic candidate-edge
  requiredness differs between schema and edge table, the committed generator
  does not reproduce the frozen artifacts, and the immutable preparation
  commit contains consumers omitted by the positive witness.
-/

namespace ToeFormal.Release.LoopControlRegistryShardingReadOnlyPrototypeExecutionPacketV2IndependentReview

def preparationCommit : String :=
  "0138ba751ef2ae1b08347a3089da077c5a694550"

def preparationParentCommit : String :=
  "81a3555a1f83a37ec01bacc247f45d1a5bfe8430"

def packetSha256 : String :=
  "8381ae2101610eab7ae307e4c3849efbe1a1d9786b4edee7702f70d2662b723a"

def contractBundleSha256 : String :=
  "36d7bdfe8f03e0e6cceb2fd653b98f0f0f26fcadaf40ff53a0dc2450b4f04432"

def declaredSchemaEdgeRootSha256 : String :=
  "55c46d8c7347473e6c6578e4f79fc8f5b670a1172f512903cfabe7d5ce90988c"

def independentlyDerivedSchemaEdgeRootSha256 : String :=
  "1db029814955bab15a248aa2bb9f61a67a2faa3a4c1fcaca4169878756ff989c"

def independentReviewSha256 : String :=
  "1a82c3681658b11d1bc477ba3c61079be6d3b93bad30135d9bd6e0870b82953e"

def declaredSchemaEdgeCount : Nat := 111
def independentlyDerivedSchemaEdgeCount : Nat := 111
def dynamicRequirednessMismatchCount : Nat := 14
def retainedV1RegressionCount : Nat := 12
def newV2RegressionCount : Nat := 15
def permanentRegressionCount : Nat := 27
def historyRecordCount : Nat := 4691
def historyShardCount : Nat := 14
def preparationConsumerCallsiteCount : Nat := 592
def modelSourceConsumerCallsiteCount : Nat := 584
def blockingFindingCount : Nat := 3

def schemaEdgeTablesEqual : Bool := false
def frozenArtifactsReproducedByCommittedGenerator : Bool := false
def preparationInventoryEqualsModelSourceInventory : Bool := false
def byteExactCustodyReconstruction : Bool := true
def stageAAuthorized : Bool := false
def stageBAuthorized : Bool := false
def versionedV3SuccessorRequired : Bool := true
def prototypeExecutionOccurred : Bool := false
def registryMigrationOccurred : Bool := false
def authorityCutoverOccurred : Bool := false
def unitLedgerExecuted : Bool := false
def scientificClaimPromoted : Bool := false

theorem regressionAndCustodyScaleReconciles :
    retainedV1RegressionCount + newV2RegressionCount = permanentRegressionCount ∧
      historyRecordCount = 4691 ∧
      historyShardCount = 14 := by
  decide

theorem independentlyObservedPreparationDelta :
    modelSourceConsumerCallsiteCount + 8 = preparationConsumerCallsiteCount ∧
      dynamicRequirednessMismatchCount = 14 := by
  decide

theorem blockedReviewBoundary :
    schemaEdgeTablesEqual = false ∧
      frozenArtifactsReproducedByCommittedGenerator = false ∧
      preparationInventoryEqualsModelSourceInventory = false ∧
      byteExactCustodyReconstruction = true ∧
      stageAAuthorized = false ∧
      stageBAuthorized = false ∧
      versionedV3SuccessorRequired = true ∧
      prototypeExecutionOccurred = false ∧
      registryMigrationOccurred = false ∧
      authorityCutoverOccurred = false ∧
      unitLedgerExecuted = false ∧
      scientificClaimPromoted = false := by
  decide

end ToeFormal.Release.LoopControlRegistryShardingReadOnlyPrototypeExecutionPacketV2IndependentReview
