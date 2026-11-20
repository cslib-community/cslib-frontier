/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.PCP.TwoProverGame.Anchoring
import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredDependency
import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredConditioning
import CslibFrontier.Computability.PCP.TwoProverGame.GameAlgebraPerfect
import CslibFrontier.Computability.PCP.TwoProverGame.LinearSystem
import CslibFrontier.Computability.PCP.TwoProverGame.Synchronous
import CslibFrontier.Foundations.Algebra.Group.HomomorphismTesting
import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumEntropy
import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumInformationChain
import CslibFrontier.Foundations.Quantum.DensityMatrix.PurificationOverlap
import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropy
import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropyConvexity
import CslibFrontier.Foundations.Quantum.DensityMatrix.RelativeEntropyDataProcessing
import CslibFrontier.Foundations.Quantum.DensityMatrix.QuantumRaz
import CslibFrontier.Foundations.Quantum.DensityMatrix.FidelityTraceDistance
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PowersStormer
import CslibFrontier.Probability.MarkovChain.RandomWalk
import CslibFrontier.Probability.MarkovChain.RotationMap
import CslibFrontier.Probability.PairwiseIndependentHash.Retention
import CslibFrontier.Probability.SmallBias.Code
import CslibFrontier.Probability.SmallBias.Degree
import CslibFrontier.Foundations.Combinatorics.Expander.Visits
import CslibFrontier.Foundations.Combinatorics.Expander.HittingProduct
import CslibFrontier.Foundations.Combinatorics.Expander.VisitCount
import CslibFrontier.Computability.Complexity.Classes.Padding.Tally
import CslibFrontier.Computability.Complexity.Problems.Bipartite.LogSpace
import CslibFrontier.Computability.Complexity.Problems.BoundedSTCON.Membership
import CslibFrontier.Computability.Complexity.Problems.UCONN
import CslibFrontier.Computability.Complexity.Problems.UDistance.Completeness
import CslibFrontier.Computability.Complexity.Problems.Permanent.Valiant
import CslibFrontier.Computability.Complexity.Problems.ThreeSAT.Collapse
import CslibFrontier.Computability.Complexity.Problems.ThreeSAT.Tautology
import CslibFrontier.Computability.Complexity.Classes.Sparse.Envelope
import CslibFrontier.Computability.Complexity.Classes.Advice.OneBit
import CslibFrontier.Computability.Complexity.Classes.Advice.LengthComparison
import CslibFrontier.Computability.Circuit.Boolean.Advice.Hierarchy
import CslibFrontier.Algorithms.Lean.Arborescence.PolyTime
import CslibFrontier.Algorithms.Lean.DFS.SCC
import CslibFrontier.Algorithms.Lean.DyadicRecovery
import CslibFrontier.Algorithms.Lean.MaxDicut.GoemansWilliamson
import CslibFrontier.Algorithms.Lean.MaxTwoSAT.GoemansWilliamson
import CslibFrontier.Algorithms.Lean.MaxTwoSAT.GoemansWilliamsonMaxTwoSAT
import CslibFrontier.Algorithms.Lean.TwoSAT
import CslibFrontier.Algorithms.Lean.TrimmedYates
import CslibFrontier.Algorithms.LinearAlgebra.BareissElimination
import CslibFrontier.Algorithms.Lean.TreeDecomposition.CSP
import CslibFrontier.Algorithms.WordRAM.Schoening.Amplify
import CslibFrontier.Crypto.Computational.Encryption.IVStream.Malleability
import CslibFrontier.Crypto.Computational.RSACRT
import CslibFrontier.Crypto.Game.SecondPreimage
import CslibFrontier.Crypto.Primitives.IdealCipher.Compression
import CslibFrontier.Crypto.Primitives.IdealCipher.CompressionVariants
import CslibFrontier.Crypto.Primitives.PRF.RandomOracleModel
import CslibFrontier.Crypto.Protocols.Cipher.LinearCryptanalysis
import CslibFrontier.Crypto.Protocols.MAC.GHASH
import CslibFrontier.Probability.HashFamily.Polynomial
import CslibFrontier.Computability.QueryComplexity.MajorityThree
import CslibFrontier.Computability.QueryComplexity.Randomized.Nisan
import CslibFrontier.Computability.QueryComplexity.YaoExpected
import CslibFrontier.Computability.Complexity.Problems.SharpCycle
import CslibFrontier.Computability.Complexity.Problems.StronglyConnected.Completeness

import CslibFrontier.Computability.QueryComplexity.AdjacentPair
import CslibFrontier.Crypto.Computational.Stretch.Prefix
import CslibFrontier.Crypto.Computational.SchnorrLeakedNonce
import CslibFrontier.Crypto.Protocols.MPC.Beaver
import CslibFrontier.Crypto.Protocols.OPRF.DiffieHellman
import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Generic
import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Recognition
import CslibFrontier.Crypto.Protocols.SigmaProtocol.LanguageReduction
import CslibFrontier.Crypto.Protocols.SigmaProtocol.LanguageReduction.Efficient
import CslibFrontier.Crypto.Protocols.SigmaProtocol.LanguageReduction.Sound
import CslibFrontier.Crypto.Protocols.SigmaProtocol.UniqueResponses
import CslibFrontier.Computability.Complexity.ProofSystem.Exhaustive
import CslibFrontier.Computability.Circuit.Arithmetic.BitBlast
import CslibFrontier.Computability.Circuit.Arithmetic.CircuitLowerBound
import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.LowerBound
import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.UpperBound
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.AnyOrder
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Basic
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ConstantDepth
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ConcentratingShiftSet
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.LowerBound
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.NoncommABP
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ROABP
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.SetMultilinear
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Sparse
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.SparseOrbit
import CslibFrontier.Computability.Circuit.Arithmetic.MatrixMultiplication.NineQuarters
import CslibFrontier.Computability.Circuit.Boolean.ArithmeticRing
import CslibFrontier.Computability.Circuit.Boolean.Arithmetic
import CslibFrontier.Computability.Circuit.Boolean.BitBlastCompiler
import CslibFrontier.Computability.Circuit.Boolean.FiniteSimulation
import CslibFrontier.Computability.Circuit.Boolean.BarringtonClass
import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.AgreementLimit
import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.RandomFunction
import CslibFrontier.Computability.Circuit.Boolean.ParityNC1
import CslibFrontier.Computability.Circuit.Boolean.Braverman.Fooling
import CslibFrontier.Computability.Circuit.Boolean.Formula.Andreev
import CslibFrontier.Computability.Circuit.Boolean.Hastad.Sharp
import CslibFrontier.Computability.Circuit.Boolean.FormalComplexityMeasure
import CslibFrontier.Computability.Circuit.Boolean.Khrapchenko
import CslibFrontier.Computability.Circuit.Boolean.NaturalProof.Generator
import CslibFrontier.Computability.Circuit.Boolean.NaturalProof.Restriction
import CslibFrontier.Computability.Circuit.Boolean.NonuniformSeparation
import CslibFrontier.Computability.Circuit.Boolean.Razborov.MiddleSlice.P
import CslibFrontier.Computability.Circuit.Boolean.Razborov.Useful
import CslibFrontier.Computability.Circuit.Boolean.Smolensky
import CslibFrontier.Foundations.BooleanAnalysis.OrDegree
import CslibFrontier.Computability.Circuit.NNF.Negation.Separation
import CslibFrontier.Computability.Communication.CliqueIndependentSet
import CslibFrontier.Computability.Communication.AhoUllmanYannakakis
import CslibFrontier.Computability.Communication.Discrepancy
import CslibFrontier.Computability.Communication.Discrepancy.Spectral
import CslibFrontier.Computability.Communication.DistinctRows
import CslibFrontier.Computability.Communication.Disjointness
import CslibFrontier.Computability.Communication.FoolingSet
import CslibFrontier.Computability.Communication.Rank
import CslibFrontier.Computability.Communication.Nondeterministic.UniqueDisjointness
import CslibFrontier.Computability.Complexity.Classes.Alternation.DeterministicTime
import CslibFrontier.Computability.Complexity.Classes.Alternation.Savitch
import CslibFrontier.Computability.Complexity.Classes.Alternation.SpaceGame
import CslibFrontier.Computability.Complexity.Classes.BQP.Counting
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.NondeterministicSpace
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Space
import CslibFrontier.Computability.Complexity.Classes.Space.Separation
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Translational
import CslibFrontier.Computability.Complexity.Classes.IP.Deterministic
import CslibFrontier.Computability.Complexity.Classes.IP.PerfectSoundness
import CslibFrontier.Computability.Complexity.Classes.IP.Shamir
import CslibFrontier.Computability.Complexity.Classes.Ladner.Density
import CslibFrontier.Computability.Complexity.Classes.LogSpace.Complement
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.DeterministicTransitiveClosure
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.DeterministicTransitiveClosure.Converse
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.Reachability
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.TransitiveClosure
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.TransitiveClosure.Converse
import CslibFrontier.Computability.Complexity.Classes.LogSpace.PolyTime
import CslibFrontier.Computability.Complexity.Classes.LogSpace.USTCON
import CslibFrontier.Computability.Complexity.Classes.Oracle.BakerGillSolovay
import CslibFrontier.Computability.Complexity.Classes.Oracle.FewQueries
import CslibFrontier.Computability.Complexity.Classes.PCP.ProofLocations
import CslibFrontier.Computability.Complexity.Classes.PH.OracleCollapse
import CslibFrontier.Computability.Complexity.Classes.PH.SipserLautemann
import CslibFrontier.Computability.Complexity.Classes.PH.Yap
import CslibFrontier.Computability.Complexity.Classes.Promise.CoinSplit
import CslibFrontier.Computability.Complexity.Classes.SharpP.ApproximateCounting
import CslibFrontier.Computability.Complexity.Classes.SharpP.Lowness
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic.DeterministicTime
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic.Savitch
import CslibFrontier.Computability.Complexity.Classes.Space.Savitch
import CslibFrontier.Computability.Complexity.Classes.TFNP.SelfReducibility
import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.PotentialLineCollapse
import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.PotentialLineNormalization
import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.SOPLCollapse
import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.SpernerHardness
import CslibFrontier.Computability.Complexity.Classes.TFNP.Uncheckable
import CslibFrontier.Computability.Complexity.Classes.Time.LasVegas
import CslibFrontier.Computability.Complexity.Classes.Time.Sublinear
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Williams
import CslibFrontier.Computability.Complexity.Classes.Toda
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Fagin.Converse
import CslibFrontier.Computability.Complexity.Fagin.Ordered.Completeness
import CslibFrontier.Computability.Complexity.Fagin.Ordered.Problems
import CslibFrontier.Computability.Complexity.FineGrained.CliqueGrouping
import CslibFrontier.Computability.Complexity.FineGrained.CountingNativeEndpoint
import CslibFrontier.Computability.Complexity.FineGrained.CountingNativeModelCount
import CslibFrontier.Computability.Complexity.FineGrained.OrthogonalVectors
import CslibFrontier.Computability.Complexity.FineGrained.PPZ
import CslibFrontier.Computability.Complexity.FineGrained.Schoening
import CslibFrontier.Computability.Complexity.FineGrained.SchoeningMachine
import CslibFrontier.Computability.Complexity.FineGrained.Sparsification
import CslibFrontier.Computability.Complexity.Gradel
import CslibFrontier.Computability.Complexity.ImmermanVardi
import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.XP
import CslibFrontier.Computability.Complexity.Problems.BoundedTermination
import CslibFrontier.Computability.Complexity.Problems.Hamiltonian.AnyEndpoints
import CslibFrontier.Computability.Complexity.Problems.HornSAT
import CslibFrontier.Computability.Complexity.Problems.IndependentSet.Exact
import CslibFrontier.Computability.Complexity.Problems.IndependentSet.ExactCompleteness
import CslibFrontier.Computability.Complexity.Problems.QUADEQ
import CslibFrontier.Computability.Complexity.Problems.Permanent.ThreeSAT
import CslibFrontier.Computability.Complexity.Problems.Primes
import CslibFrontier.Computability.Complexity.Problems.TMSAT
import CslibFrontier.Computability.Complexity.Problems.ThreeExactCover
import CslibFrontier.Computability.Complexity.Problems.TwoSAT.PolyTime
import CslibFrontier.Computability.Complexity.Problems.XSAT
import CslibFrontier.Computability.Complexity.Problems.Permanent.ZeroOne
import CslibFrontier.Computability.Complexity.Problems.Permanent.Nonnegative
import CslibFrontier.Computability.Kolmogorov.Incompleteness
import CslibFrontier.Computability.Kolmogorov.MINKT
import CslibFrontier.Computability.Kolmogorov.MINKTStar.Hardness
import CslibFrontier.Computability.Kolmogorov.MKtP
import CslibFrontier.Computability.Kolmogorov.SymmetryOfInformation
import CslibFrontier.Computability.Kolmogorov.UniversalMachine
import CslibFrontier.Computability.MCSP.AntiChecker
import CslibFrontier.Computability.MCSP.AntiChecker.Efficient
import CslibFrontier.Computability.MCSP.FormulaMagnification
import CslibFrontier.Computability.MCSP.FormulaMagnification.AverageCase
import CslibFrontier.Computability.MCSP.FormulaMagnification.Locality
import CslibFrontier.Computability.MCSP.FormulaMagnification.StretchedExponential
import CslibFrontier.Computability.MCSP.FormulaMagnification.Subexponential
import CslibFrontier.Computability.MCSP.FormulaMagnification.SublinearAverageCase
import CslibFrontier.Computability.MCSP.HardnessConsequences
import CslibFrontier.Computability.MCSP.Magnification
import CslibFrontier.Computability.MCSP.Magnification.AntiChecker
import CslibFrontier.Computability.MCSP.Magnification.GapMCSP
import CslibFrontier.Computability.MCSP.Magnification.MergeTree.Locality
import CslibFrontier.Computability.MCSP.MultiNPHard
import CslibFrontier.Computability.MCSP.PartialETH
import CslibFrontier.Computability.MCSP.PartialHardness.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.StepCounter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Countable
import CslibFrontier.Computability.PCP.Approximation.FGLSS
import CslibFrontier.Computability.PCP.Approximation.GapLin
import CslibFrontier.Computability.PCP.Approximation.MaxCSP.UpperBounds
import CslibFrontier.Computability.PCP.Approximation.UniqueGames.Complexity
import CslibFrontier.Computability.PCP.Completeness
import CslibFrontier.Computability.PolyTime.LinearAlgebra.RationalElimination
import CslibFrontier.Computability.QueryComplexity.RelevantCoordinates
import CslibFrontier.Computability.QueryComplexity.Connectivity
import CslibFrontier.Computability.QueryComplexity.Quantum.NayakWuConsequences
import CslibFrontier.Computability.QueryComplexity.Quantum.PermutationInversion
import CslibFrontier.Computability.QueryComplexity.Quantum.SpectralAdversary
import CslibFrontier.Computability.QueryComplexity.Quantum.WeightedAdversary
import CslibFrontier.Crypto.Computational.ChaumPedersenProtocol
import CslibFrontier.Crypto.Computational.CollisionResistant.Birthday
import CslibFrontier.Crypto.Computational.CollisionResistant.BruteForce
import CslibFrontier.Crypto.Computational.CramerShoup.Decodable
import CslibFrontier.Crypto.Computational.CramerShoup.ProjectiveHash
import CslibFrontier.Crypto.Computational.CramerShoup.ProjectiveHash.Games
import CslibFrontier.Crypto.Computational.DictionarySearch
import CslibFrontier.Crypto.Computational.DiffieHellman.BlindedFamily
import CslibFrontier.Crypto.Computational.DiffieHellman.MultiDDH
import CslibFrontier.Crypto.Computational.DiffieHellman.SelfReduction.Family
import CslibFrontier.Crypto.Computational.ElGamal.KDF
import CslibFrontier.Crypto.Computational.SchnorrGuessing
import CslibFrontier.Crypto.Computational.DiffieHellman.ListCDHFamily
import CslibFrontier.Crypto.Computational.DiffieHellman.Order
import CslibFrontier.Crypto.Computational.DiscreteLog.Interpolation
import CslibFrontier.Crypto.Computational.ElGamal.Decodable
import CslibFrontier.Crypto.Computational.ElGamal.OneWay
import CslibFrontier.Crypto.Computational.ElGamal.ProbComp
import CslibFrontier.Crypto.Computational.ElGamal.Unpredictable
import CslibFrontier.Crypto.Computational.Encryption.CBCMode.Uniform
import CslibFrontier.Crypto.Computational.Encryption.CTRMode.Uniform
import CslibFrontier.Crypto.Computational.Encryption.ECB
import CslibFrontier.Crypto.Computational.Encryption.Hybrid
import CslibFrontier.Crypto.Computational.Encryption.OFBMode.Uniform
import CslibFrontier.Crypto.Computational.Encryption.Authenticated
import CslibFrontier.Crypto.Computational.Encryption.Nested
import CslibFrontier.Crypto.Computational.Encryption.RepeatingCiphertexts
import CslibFrontier.Crypto.Computational.Encryption.CCA.Malleability
import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC.PartialTag
import CslibFrontier.Crypto.Computational.Encryption.MACThenEncrypt.EncForge
import CslibFrontier.Crypto.Computational.Encryption.Cipher.Perfect
import CslibFrontier.Crypto.Computational.Encryption.MessageRecovery
import CslibFrontier.Crypto.Computational.Encryption.ParityPrediction
import CslibFrontier.Crypto.Computational.Encryption.Functional
import CslibFrontier.Crypto.Computational.GenericGroup.BabyStepGiantStep
import CslibFrontier.Crypto.Computational.GenericGroup.RecursiveDlog
import CslibFrontier.Crypto.Computational.GoldreichLevin.HardCore
import CslibFrontier.Crypto.Computational.HardCore.NoUniversal
import CslibFrontier.Crypto.Computational.InaccessibleEntropy.OneWay
import CslibFrontier.Crypto.Primitives.PRG.ReadOnceBias
import CslibFrontier.Crypto.Computational.InaccessibleEntropy.TargetCollision
import CslibFrontier.Crypto.Computational.IndexedSignature.Counter
import CslibFrontier.Crypto.Computational.KeyExchange.KeyGuessing
import CslibFrontier.Crypto.Computational.LubyRackoff
import CslibFrontier.Crypto.Computational.MAC
import CslibFrontier.Crypto.Computational.MerkleDamgard.LengthStrengthened
import CslibFrontier.Crypto.Computational.MerkleTree.Binding
import CslibFrontier.Crypto.Computational.NaorYungUOWHF
import CslibFrontier.Crypto.Computational.Nonuniform.ZeroKnowledge
import CslibFrontier.Crypto.Computational.OneTimeSignature.ContainmentFree
import CslibFrontier.Crypto.Computational.OneTimeSignature.DominationFree
import CslibFrontier.Crypto.Computational.OneWay.Iterate
import CslibFrontier.Crypto.Computational.OneWay.IterateCounterexample
import CslibFrontier.Crypto.Computational.OneWay.LengthPreserving
import CslibFrontier.Crypto.Computational.OneWay.LiuPass
import CslibFrontier.Crypto.Computational.OneWay.MCSP
import CslibFrontier.Crypto.Computational.OneWay.Repeated
import CslibFrontier.Crypto.Computational.OneWay.WeakNotStrong
import CslibFrontier.Crypto.Computational.OneWayToPRF
import CslibFrontier.Crypto.Computational.OneWayToPRG
import CslibFrontier.Crypto.Computational.PedersenCommitment
import CslibFrontier.Crypto.Computational.PedersenCommitment.ProbComp
import CslibFrontier.Crypto.Computational.PseudorandomFunction.ToPRG
import CslibFrontier.Crypto.Computational.SchnorrEavesdrop
import CslibFrontier.Crypto.Computational.SchnorrProtocol
import CslibFrontier.Crypto.Computational.PseudorandomGenerator.Parallel
import CslibFrontier.Crypto.Computational.PseudorandomPermutation
import CslibFrontier.Crypto.Computational.PseudorandomPermutation.BirthdayAttack
import CslibFrontier.Crypto.Computational.RSACommonRoot
import CslibFrontier.Crypto.Computational.RSAHalfPredicate
import CslibFrontier.Crypto.Computational.RSAHash
import CslibFrontier.Crypto.Computational.RSAUnitInversion
import CslibFrontier.Crypto.Computational.RSAUnitInversion.Converse
import CslibFrontier.Crypto.Computational.SIS.Ajtai
import CslibFrontier.Crypto.Computational.SecondPreimageResistant.Relations
import CslibFrontier.Crypto.Computational.SecondPreimageResistant.XorTarget
import CslibFrontier.Crypto.Computational.TCRSignature.ManyTime
import CslibFrontier.Crypto.Primitives.PRP.BirthdayAttack
import CslibFrontier.Crypto.Primitives.PRP.Finite
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Bot
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.WordSecurity
import CslibFrontier.Crypto.Protocols.MPC.ProductRelation
import CslibFrontier.Crypto.Protocols.MPC.ProductRelation.Privacy
import CslibFrontier.Crypto.Protocols.PIR.Block
import CslibFrontier.Crypto.Protocols.PIR.Collusion
import CslibFrontier.Crypto.Protocols.PIR.GeneralCover
import CslibFrontier.Crypto.Protocols.PIR.Indexed
import CslibFrontier.Crypto.Protocols.PIR.Interactive
import CslibFrontier.Crypto.Protocols.PIR.MultiInteractive
import CslibFrontier.Crypto.Protocols.PIR.Shamir
import CslibFrontier.Crypto.Protocols.PIR.SmoothConverse
import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.LinearEquivalence
import CslibFrontier.Crypto.Protocols.SigmaProtocol.Efficient
import CslibFrontier.Crypto.Computational.ElGamal.Homomorphism
import CslibFrontier.Crypto.Computational.DiffieHellman.CyclicGroupFamily
import CslibFrontier.Crypto.Computational.ElGamal.StronglyUnpredictable
import CslibFrontier.Crypto.Computational.Factoring.WeakModuli
import CslibFrontier.Crypto.Computational.GenericGroup.DiffieHellman
import CslibFrontier.Crypto.Computational.GenericGroup.DiscreteLog
import CslibFrontier.Crypto.Computational.OneTimeSignature.ContainmentFree
import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.Correlation
import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.Cut
import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.StableSet
import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.TSP
import CslibFrontier.DataStructure.Dictionary.UniformProbing
import CslibFrontier.DataStructure.NearNeighbor.Angular
import CslibFrontier.DataStructure.NearNeighbor.PStable
import CslibFrontier.DataStructure.Paging.Marking
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.RootBound
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.Sturm
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.TotalIsolation
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.CFI
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.ColorRefinement
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.WeisfeilerLeman
import CslibFrontier.Foundations.Computability.KleenePost
import CslibFrontier.Foundations.Computability.KleenePostJump
import CslibFrontier.Foundations.Data.BranchingVector
import CslibFrontier.GameTheory.Bimatrix.Existence
import CslibFrontier.GameTheory.Bimatrix.PPAD
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Cycle
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Dictatorship
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Interval
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Median
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Tree
import CslibFrontier.GameTheory.Strategic.Correlated
import CslibFrontier.GameTheory.Strategic.Nash
import CslibFrontier.GameTheory.Strategic.SwapRegretDynamics
import CslibFrontier.Logics.Propositional.CNF.TruthTable
import CslibFrontier.Logics.Propositional.PlaistedGreenbaumCNF
import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Connectivity
import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.FiniteLinearOrder
import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.GraphProperties
import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Hintikka
import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Monadic
import CslibFrontier.Logics.FirstOrder.FiniteVariable.CFI
import CslibFrontier.Logics.FirstOrder.FiniteVariable.ColorRefinement
import CslibFrontier.Logics.FirstOrder.FiniteVariable.CountingHintikka
import CslibFrontier.Logics.FirstOrder.FiniteVariable.Hintikka
import CslibFrontier.Logics.FirstOrder.FiniteVariable.Infinitary
import CslibFrontier.Logics.FirstOrder.FiniteVariable.WeisfeilerLeman
import CslibFrontier.Logics.FirstOrder.Locality.GraphProperties
import CslibFrontier.Logics.FirstOrder.Locality.Hanf
import CslibFrontier.Logics.FirstOrder.Locality.Reachability
import CslibFrontier.Logics.FirstOrder.Locality.Sharp
import CslibFrontier.Logics.FirstOrder.Operator.TransitiveClosure.Expressiveness
import CslibFrontier.Logics.FirstOrder.Ordered.Problems.CNF
import CslibFrontier.Logics.FirstOrder.Ordered.Problems.Coloring
import CslibFrontier.Logics.FirstOrder.Ordered.Problems.IndependentSetReduction
import CslibFrontier.Logics.FirstOrder.Ordered.Problems.SizedGraph
import CslibFrontier.Logics.FirstOrder.Ordered.Projection.Reduction
import CslibFrontier.Logics.FirstOrder.Trakhtenbrot.Binary
import CslibFrontier.Logics.FirstOrder.Trakhtenbrot.Sentence
import CslibFrontier.Logics.FirstOrder.Trakhtenbrot.Undecidability
import CslibFrontier.Logics.FirstOrder.ZeroOneLaw
import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.BinomialRandomGraph
import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Infinitary
import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Rado
import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Relational
import CslibFrontier.Logics.Propositional.CNF.Branching
import CslibFrontier.Logics.Propositional.Resolution.Pigeonhole
import CslibFrontier.Logics.SecondOrder.Ordered.Grounding
import CslibFrontier.Logics.SecondOrder.WordMSO.McNaughtonPapert
import CslibFrontier.Logics.SecondOrder.WordMSO.OfRegular
import CslibFrontier.Logics.SecondOrder.WordMSO.Separation
import CslibFrontier.Logics.SecondOrder.WordMSO.StarFree
import CslibFrontier.MachineLearning.Boosting.AdaBoost
import CslibFrontier.MachineLearning.LossMinimization.RLM
import CslibFrontier.MachineLearning.LossMinimization.Squared
import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.VCDimension
import CslibFrontier.MachineLearning.OnlineLearning.SwapRegret
import CslibFrontier.MachineLearning.PACBayes.Basic
import CslibFrontier.MachineLearning.PACBayes.KL
import CslibFrontier.MachineLearning.PACLearning.AgnosticVCSharp
import CslibFrontier.MachineLearning.PACLearning.FundamentalTheorem
import CslibFrontier.MachineLearning.PACLearning.MDL
import CslibFrontier.MachineLearning.PACLearning.NatarajanDimension
import CslibFrontier.MachineLearning.PACLearning.Nonuniform
import CslibFrontier.MachineLearning.UniformLearning.CIKK.AC0Mod
import CslibFrontier.MachineLearning.UniformLearning.CIKK.Amplification
import CslibFrontier.MachineLearning.UniformLearning.CIKK.Complexity
import CslibFrontier.MachineLearning.UniformLearning.CIKK.Learner
import CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.GGM
import CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.NaturalProperty
import CslibFrontier.MachineLearning.UniformLearning.NisanWigderson
import CslibFrontier.MachineLearning.UniformLearning.NisanWigderson.BestOf
import CslibFrontier.Computability.Probabilistic.CoinOfDigits
import CslibFrontier.Probability.BilinearFingerprint
import CslibFrontier.Probability.Extractor.LeftoverHash
import CslibFrontier.Probability.Extractor.TwoSource
import CslibFrontier.Probability.Fooling.DecisionTree
import CslibFrontier.Probability.LocalitySensitiveHash.PStable
import CslibFrontier.Probability.LocalitySensitiveHash.SimHash
import CslibFrontier.Foundations.Data.Code.LowDegreeExtension
import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.ExponentialDesign
import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization.NonExplicitPRG
import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Derandomization
import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.SetLowerBound
import CslibFrontier.Computability.Complexity.Problems.ModularSquareRoot
import CslibFrontier.Computability.Automata.MPDA.OneHole
import CslibFrontier.Computability.Automata.MPDA.WellNested
import CslibFrontier.Crypto.Computational.PseudorandomGenerator.ModReduction
import CslibFrontier.Crypto.Computational.StatisticalIndistinguishability
import CslibFrontier.Crypto.Primitives.PRG.LinearCongruential
import CslibFrontier.Crypto.Protocols.PerfectSecrecy.Characterization
import CslibFrontier.Crypto.Protocols.PerfectSecrecy.ShannonCiphers
import CslibFrontier.Algorithms.Lean.CDCL.System
import CslibFrontier.Algorithms.Lean.DPLL.RefutationSize

/-!
# Collected results

These scopes and source correspondences were inspected against existing repository statements
and citations. They are not a new primary-source audit. `unverified` means a source theorem
name/number or precise locator has not yet been collected; it must not be guessed.

## Headline results

The results that the curated formal abstracts selected until their retirement on 2026-11-08,
registered against the library theorems that the abstracts' bridges applied. A group whose
theorems live in several modules is split into one entry per module. Bibliography keys come from
the citations of the defining modules. The depth-two threshold bounds for Andreev's function are
left out: they are original results, which `results/README.md` admits only once original results
have an explicit representation.
-/

register_result "connectivity-evasiveness" where
  title := "Graph connectivity requires every possible edge query"
  topic := "query complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 11.4 (2007 public draft)",
      locator := "2007 public draft, PDF 228 / printed p. 212" }
  ]
  theorems := [Cslib.BitString.Graph.complexity_connectivity]
  scope := "For every m, the total connectivity function on labelled undirected simple graphs \
    on Fin m has deterministic decision-tree complexity m.choose 2. Each input coordinate \
    represents one unordered pair of distinct vertices; repeated queries are allowed. Mathlib \
    regards the empty graph as disconnected and the one-vertex graph as connected, and both \
    functions have complexity zero. No graph promise, arbitrary edge-permutation symmetry, \
    randomized bound or machine-runtime bound is asserted."

register_result "cook-levin" where
  title := "Cook–Levin: SAT is NP-complete"
  topic := "NP-completeness"
  sources := [
    { paper := AroraBarak09, theorem := unverified, locator := unverified },
    { paper := Papadimitriou94, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.CookLevin.SAT_npComplete,
    Cslib.Complexity.CookLevin.UNSAT_coNPComplete
  ]
  scope := "SAT and UNSAT over CNF formulas with natural-number variables under the explicit \
    framed encoding encCNF. NP uses one native multi-tape polynomial-time verifier with \
    certificates of exact polynomial length; hardness is under total native polynomial-time \
    many-one reductions from problems with arbitrary injective encodings. UNSAT \
    coNP-completeness follows by complementation."

register_result "tmsat-np-complete" where
  title := "TMSAT is NP-complete"
  topic := "NP-completeness"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 2.9",
      locator := "Web draft 2007-01-08, printed p. 44; PDF p. 60" }
  ]
  theorems := [Cslib.Complexity.TMSAT.npComplete]
  scope := "Instances (α, x, 1^n, 1^t) as the structure TMSATInstance under encTMSATInstance, \
    with the native machine description, raw input bits and unary n and t. Acceptance is a \
    halted run with output [true] of the universal interpreter for t steps on frame x ++ u, \
    for a witness u of exactly n bits. Hardness for every NP problem and instance encoding."

register_result "truth-table-cnf-size" where
  title := "Every Boolean function has a CNF with at most ℓ·2^ℓ AND/OR symbols"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Claim 2.14",
      locator := "Web draft 2007-01-08, printed p. 46; PDF p. 62" }
  ]
  theorems := [Cslib.Logic.PL.CNF.exists_eval_eq_connectiveCount_le]
  scope := "Functions (Fin ℓ → Bool) → Bool and list CNFs over Fin ℓ. The size measure \
    connectiveCount counts binary connectives: k - 1 ORs per clause of k literals and m - 1 \
    ANDs between m clauses. The source's size ℓ·2^ℓ is read as an upper bound."

register_result "dir-ham-path-any-np-complete" where
  title := "Directed Hamiltonian path without given endpoints is NP-complete"
  topic := "NP-completeness"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 2.18",
      locator := "Web draft 2007-01-08, printed p. 52; PDF p. 68" }
  ]
  theorems := [Cslib.Complexity.DirHamPathAny_npComplete]
  scope := "Finite listed graphs under encGraph with some Hamiltonian path; graphs without \
    declared vertices are not members. Hardness reduces the designated-endpoint DirHamPath \
    (Sipser's diamond construction) by adding a fresh source and sink, not the draft's \
    direct 3SAT reduction."

register_result "quadeq-np-complete" where
  title := "QUADEQ is NP-complete"
  topic := "NP-completeness"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 2, Exercise 18",
      locator := "Web draft 2007-01-08, printed p. 64; PDF p. 80" }
  ]
  theorems := [Cslib.Complexity.QUADEQ_npComplete]
  scope := "Systems of quadratic equations over 𝔽₂ as lists of QuadEquation records under \
    QUADEQ.encoding: each equation lists the monomials u_i u_j with a_ij = 1, repeated \
    monomials cancelling in pairs, with binary natural-number variable labels and no bound on \
    their values. Membership by a polynomial-time verifier with first-occurrence certificates; \
    hardness by a polynomial-time reduction from SAT (the exercise's hint), composed with \
    Cook–Levin."

register_result "goldreich-three-exact-cover" where
  title := "3-Exact Cover is NP-complete"
  topic := "NP-completeness"
  sources := [
    { paper := Goldreich2006DraftR1, theorem := "Proposition 2.25",
      locator := "December 2006 r1.pdf, printed p. 85; PDF p. 110" }
  ]
  theorems := [Cslib.Complexity.ThreeExactCover_npComplete]
  scope := "Instances are lists of sets, each a list of three distinct natural numbers, under \
    the Set Cover encoding encNatSetList with binary labels. The universe is the union of the \
    sets, and a yes-instance has a sub-collection drawn from the instance covering every \
    element exactly once, with no bound on the number of chosen sets. Native NP and native \
    polynomial-time Karp reductions. Hardness reduces positive exact-three exact-one SAT with \
    at most three occurrences per variable, padding occurrence sets by windows of consecutive \
    dummy elements, instead of the draft's chain through 3SC and 3XC'. The remark on Exact \
    Cover with arbitrary set sizes is not covered. Outside-fleet source check: \
    https://github.com/cslib-community/cslib-frontier/pull/6302#pullrequestreview-5947915507"

register_result "goldreich-pc-not-self-reducible" where
  title := "If P ≠ NP ∩ coNP, some PC search problem is not self-reducible"
  topic := "search problems"
  sources := [
    { paper := Goldreich2006DraftR1, theorem := "Exercise 2.14(1)",
      locator := "December 2006 r1.pdf, printed p. 108; PDF p. 133" }
  ]
  theorems := [Cslib.Complexity.exists_mem_FNP_not_selfReducible]
  scope := "Any instance encoding with a polynomial-time Decoder (words: Decoder.bits). The \
    relation is total, in FNP (PC) and not in FPSearch. Self-reducibility \
    (SearchSelfReducible) is a SolvesSearch solver computable in polynomial time relative to \
    the oracle language enc '' searchDomain R (Definitions 2.9 and 2.14). Outside-fleet \
    six-point source check: \
    https://github.com/cslib-community/cslib-frontier/pull/6410#pullrequestreview-5953910279"

register_result "goldreich-divisor-not-self-reducible" where
  title := "If factoring is hard, the divisor search problem is not self-reducible"
  topic := "search problems"
  sources := [
    { paper := Goldreich2006DraftR1, theorem := "Exercise 2.16",
      locator := "December 2006 r1.pdf, printed p. 108; PDF p. 133" }
  ]
  theorems := [
    Cslib.Complexity.divisorSearch_mem_FNP,
    Cslib.Complexity.not_selfReducible_divisorSearch
  ]
  scope := "Numbers in canonical binary (encNat); solutions are the binary digits of a \
    non-trivial divisor. The relation is in FNP (PC). Factoring hardness: no polynomial-time \
    function returns a non-trivial divisor of every composite (equivalently divisorSearch is \
    not in FPSearch). Neither the search problem nor its prefix decision problem S'_R \
    (PolyTimeTuringReducible) reduces to the composite numbers. Outside-fleet six-point source \
    check: \
    https://github.com/cslib-community/cslib-frontier/pull/6410#pullrequestreview-5953910279"

register_result "goldreich-self-reducibility-not-decision-property" where
  title := "Two PC relations with the same domain, one self-reducible and one not"
  topic := "search problems"
  sources := [
    { paper := Goldreich2006DraftR1, theorem := "Exercise 2.17",
      locator := "December 2006 r1.pdf, printed p. 108; PDF p. 133" }
  ]
  theorems := [Cslib.Complexity.exists_selfReducible_not_selfReducible]
  scope := "Under the factoring hardness of Exercise 2.16, the assumption the main text names \
    on printed p. 72. Witnesses: compositeSearch (each composite with itself, in FPSearch) and \
    divisorSearch, both with the composites as domain; numbers in binary (encNat). \
    Outside-fleet six-point source check: \
    https://github.com/cslib-community/cslib-frontier/pull/6410#pullrequestreview-5953910279"

register_result "goldreich-few-oracle-queries-search" where
  title := "Logarithmically many oracle queries do not help to solve PC search problems"
  topic := "search problems"
  sources := [
    { paper := Goldreich2006DraftR1, theorem := "Exercise 2.10",
      locator := "December 2006 r1.pdf, printed p. 106; PDF p. 131" }
  ]
  theorems := [
    Cslib.Complexity.mem_FPSearch_of_computableInPolyTimeWithOracleQueries_log,
    Cslib.Complexity.mem_FPSearch_of_computableInPolyTimeWithOracleQueries_of_two_pow_le
  ]
  scope := "Stated in the equivalent direct form: an FNP relation solved (SolvesSearch) in \
    polynomial time relative to an arbitrary oracle language with at most c log₂ n + c \
    requests, counted against that oracle on instances of encoded length n, is in FPSearch, \
    for every constant c. The first theorem is the exercise; the second is its general form, \
    for any request bound r with 2 ^ r n polynomially bounded. Native multitape oracle \
    machines (ComputableInPolyTimeWithOracle certificates). Outside-fleet six-point source \
    check: review 5950244269 on PR #6358."

register_result "goldreich-pf-not-subset-pc" where
  title := "PF contains search problems that are not in PC"
  topic := "search problems"
  sources := [
    { paper := Goldreich2006DraftR1, theorem := "Exercise 2.1",
      locator := "December 2006 r1.pdf, printed p. 105; PDF p. 130" }
  ]
  theorems := [Cslib.Complexity.exists_polyTimeSolvable_not_mem_FNP]
  scope := "Instances and solutions are words (encBits). PF membership is spelled out \
    (polynomial length bound and a polynomial-time SolvesSearch solver with encOption encBits \
    output), since the library's FPSearch is PF ∩ PC; PC is FNP. Witness: the guideline \
    relation for the undecidable self-halting problem. Outside-fleet six-point source check: \
    review 5953896605 on PR #6407."

register_result "pcp" where
  title := "The PCP theorem"
  topic := "interactive proofs"
  sources := [
    { paper := Dinur2007, theorem := unverified, locator := unverified },
    { paper := AroraBarak09, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.NP_eq_PCP_log
  ]
  scope := "NP = PCP(log n, 1) for every injective instance encoding. The verifier's coin \
    count, nonadaptive proof addresses and verdict are each computable in polynomial time; it \
    uses O(log n + 1) random bits and O(1) queries, with perfect completeness and soundness at \
    most one half. NP is the library's deterministic-verifier class. Construction constants \
    are large."

register_result "goldreich-pcp-effective-length" where
  title := "Effective length of adaptive PCP proofs"
  topic := "interactive proofs"
  sources := [
    { paper := Goldreich2007DraftR5, theorem := "Exercise 9.15 (adaptive bound)",
      locator := "r5.pdf; PDF pp. 66–67 / printed pp. 448–449" }
  ]
  theorems := [Cslib.DecisionTree.card_biUnion_allQueries_le]
  scope := "Bound 2^(q+r) for a fixed input, with the verifier given as its family of decision \
    trees of depth at most q indexed by the r-bit coin sequences (all answer sequences \
    counted; no compiler from adaptive machines to trees is asserted). Outside-fleet six-point \
    source check: review 5953164508 on PR #6392."

register_result "goldreich-pcp-effective-length-nonadaptive" where
  title := "Effective length of non-adaptive PCP proofs"
  topic := "interactive proofs"
  sources := [
    { paper := Goldreich2007DraftR5, theorem := "Exercise 9.15 (non-adaptive bound)",
      locator := "r5.pdf; PDF p. 67 / printed p. 449" }
  ]
  theorems := [Cslib.Complexity.IsPCPVerifier.card_toFinset_queryTable_le]
  scope := "Bound 2^r(n)·q(n) on the distinct queryTable addresses of the library's \
    PCPVerifier, n the encoded length. Outside-fleet six-point source check: review \
    5953164508 on PR #6392."

register_result "gap-two-csp-promise-pcp" where
  title := "Constant-gap gapCSP is in PCP(log, O(1))"
  topic := "interactive proofs"
  sources := [
    { paper := Goldreich2007DraftR5, theorem := "Exercise 9.25",
      locator := "r5.pdf; PDF page 70 / printed page 452; Definitions 9.14 and 9.18 checked" }
  ]
  theorems := [
    Cslib.Complexity.GapTwoCSP_restrict_mem_PromisePCP
  ]
  scope := "For every finite nonempty alphabet α and every constant c > 0, fixed before the \
    input, (GapTwoCSP α (1 - c)).restrict to well-formed graphs is in the promise class \
    PromisePCP (log n + 1) 1 under Graph.encoding encConstraintTable (unary vertex counts \
    and endpoints, framed edge lists, full constraint tables). PromisePCP is Definition 9.14 \
    with completeness on yes-instances and soundness on no-instances, with the polynomial-time \
    nonadaptive verifier and resource bounds of the library PCP on every instance. The \
    verifier samples independent fair-bit blocks; each block selects an edge index from a \
    power-of-two range and accepts on padding indices. Labels are one-hot of width |α|, so a \
    round queries 2|α| proof bits, and both inputs of a loop query the same vertex label. One \
    round rejects a no-instance with probability at least c/2, and constant repetition gives \
    soundness 1/2. Parallel edges keep multiplicity and an empty edge set has violation \
    value zero. The library unsatVal of the natural-number interpretation agrees with the \
    minimum over assignments of the declared vertices only under the well-formedness and \
    nonempty-alphabet hypotheses of Graph.unsatVal_toFiniteGraph, which this statement \
    supplies. Outside-fleet source check: \
    https://github.com/cslib-community/cslib-frontier/pull/6367#pullrequestreview-5950754049"

register_result "goldreich-fglss-independence-number-nonadaptive" where
  title := "Independence number of the FGLSS graph of a nonadaptive PCP verifier"
  topic := "interactive proofs"
  sources := [
    { paper := Goldreich2007DraftR5, theorem := "Exercise 9.18, items 2–4 and the general identity",
      locator := "r5.pdf; PDF pages 67–68 / printed pages 449–450" }
  ]
  theorems := [
    Cslib.Complexity.PCPVerifier.exists_acceptCount_eq_indepNum_fglssGraph,
    Cslib.Complexity.PCPVerifier.acceptCount_le_indepNum_fglssGraph,
    Cslib.Complexity.PCPVerifier.indepNum_fglssGraph_le,
    Cslib.Complexity.IsPCPVerifier.indepNum_fglssGraph_eq_of_mem,
    Cslib.Complexity.IsPCPVerifier.two_mul_indepNum_fglssGraph_le_of_not_mem
  ]
  scope := "For the library's nonadaptive PCPVerifier (queries depend only on the instance and \
    the coins; Goldreich allows adaptive queries), with no time certificate needed: the \
    vertices are the accepting views that answer repeated queries consistently, and edges join \
    views with different answers at a common position. Leaving out self-conflicting views \
    implements the source's inconsistency rule in a loopless graph and leaves the independent \
    sets unchanged. The independence number equals the largest number of the 2 ^ r coin \
    strings accepted with one proof, attained by a finite proof (2 ^ r · max_π Pr[V^π(x) = 1]), \
    where r is the actual coin count V.coins x. Item 2 (at most 2 ^ r) and the identity need \
    no PCP premise; item 3 (equal to 2 ^ r on members) and item 4 (2 α ≤ 2 ^ r on non-members) \
    use completeness and soundness of IsPCPVerifier. Item 1 (computing the graph in time \
    poly(2 ^ (r + q) |x|)) and the every-constant NP-hardness of Independent Set and Clique \
    are not covered. Outside-fleet six-point source check: review 5951623556 on PR #6382."

register_result "fagin" where
  title := "Fagin: logic captures NP"
  topic := "descriptive complexity"
  sources := [
    { paper := Fagin1974, theorem := unverified, locator := unverified },
    { paper := Immerman1999, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.ESO.definable_iff_isoClosed_and_queryLanguage_mem_NP
  ]
  scope := "A class of finite structures over a relational language with a finite vocabulary is \
    existential second-order definable iff it is isomorphism-closed and its query language is \
    in NP under the explicit structure encoding encStructure. No further hypotheses: empty \
    universes and nullary relations are included."

register_result "savitch" where
  title := "Savitch: NPSPACE equals PSPACE"
  topic := "space complexity"
  sources := [
    { paper := Sipser2013, theorem := unverified, locator := unverified },
    { paper := AroraBarak09, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.NPSPACE_eq_PSPACE
  ]
  scope := "Class equality for arbitrary injective encodings. PSPACE is total deterministic \
    decision by one native multi-tape machine in polynomial work space; NPSPACE uses one \
    finite-state nondeterministic machine whose every computation prefix respects a \
    polynomial space bound and whose branches all halt. The parameterized quadratic-space \
    simulation is the separate entry savitch-general."

register_result "savitch-general" where
  title := "Savitch: NSPACE(s) is contained in DSPACE(s²)"
  topic := "space complexity"
  sources := [
    { paper := Savitch1970, theorem := unverified, locator := unverified },
    { paper := Sipser2013, theorem := "Theorem 8.5",
      locator := "Section 8.4, final paragraph (p. 351)" },
    { paper := AroraBarak09, theorem := "Theorem 4.14", locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.NSPACE_subset_DSPACE_sq,
    Cslib.Complexity.mem_DSPACE_sq_of_recognizesInSpace
  ]
  scope := "NSPACE(s) ⊆ DSPACE(s²) for every s with log₂ n ≤ s(n); no constructibility \
    assumed. One finite-state native nondeterministic machine per problem, work space \
    c₁·s(n) + c₂ along every computation prefix; the recognizer form permits nonterminating \
    branches. The deterministic machine halts on every input and reads its input in place; \
    arbitrary injective encodings."

register_result "space-hierarchy" where
  title := "Stearns–Hartmanis–Lewis: the deterministic space hierarchy"
  topic := "space complexity"
  sources := [
    { paper := StearnsHartmanisLewis1965, theorem := unverified, locator := unverified },
    { paper := Sipser2013, theorem := unverified, locator := unverified },
    { paper := AroraBarak09, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.DSPACE_ssubset_DSPACE,
    Cslib.Complexity.L_ssubset_DSPACE_log2_sq
  ]
  scope := "DSPACE f ⊂ DSPACE g on binary words for space-constructible g with ⌊log₂ n⌋ ≤ g n \
    when every c·f(n)+c is eventually below g(n): the textbook gap and logarithmic threshold. \
    DSPACE is total deterministic decision by one native multi-tape machine within \
    O(s n) work cells. The nondeterministic space hierarchy is the entry nspace-hierarchy."

register_result "nspace-hierarchy" where
  title := "The nondeterministic space hierarchy"
  topic := "space complexity"
  sources := [
    { paper := Immerman1988, theorem := "Corollary 4", locator := unverified },
    { paper := Sipser2013, theorem := unverified, locator := unverified },
    { paper := Szelepcsenyi1987, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.NSPACE_ssubset_NSPACE,
    Cslib.Complexity.NL_ssubset_NSPACE_log2_sq
  ]
  scope := "NSPACE f ⊂ NSPACE g on binary words for space-constructible g with ⌊log₂ n⌋ ≤ g n \
    when every c·f(n)+c is eventually below g(n), the same hypotheses as the deterministic \
    hierarchy. NSPACE is decision by one finite-state native nondeterministic multi-tape machine \
    within c₁·s(n) + c₂ work cells along every computation prefix, every branch halting. The \
    diagonal is in NSPACE g by Immerman–Szelepcsényi complementation of a budgeted universal \
    recognizer that reads its input in place."

register_result "alternation" where
  title := "Chandra–Kozen–Stockmeyer: AP equals PSPACE"
  topic := "space complexity"
  sources := [
    { paper := ChandraKozenStockmeyer1981, theorem := unverified, locator := unverified },
    { paper := Sipser2013, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.AP_eq_PSPACE
  ]
  scope := "One finite-state alternating multi-tape machine per problem (two transition \
    functions as in Arora–Barak, least-fixed-point acceptance), every computation path halting \
    within polynomial time; PSPACE is deterministic polynomial space; arbitrary injective \
    encodings. AL = P is not included: the library proves only AL ⊆ P."

register_result "alternation-apspace-exp" where
  title := "Chandra–Kozen–Stockmeyer: APSPACE equals EXP"
  topic := "space complexity"
  sources := [
    { paper := ChandraKozenStockmeyer1981, theorem := unverified, locator := unverified },
    { paper := Sipser2013, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.APSPACE_eq_EXP
  ]
  scope := "One finite-state alternating multi-tape machine per problem with least-fixed-point \
    acceptance, polynomial work space along every computation prefix and every branch halting; \
    EXP is deterministic decision within c₁·2^(n^d) + c₂ steps, with any space bound; \
    arbitrary injective encodings."

register_result "alternation-aspace-dtime" where
  title := "Chandra–Kozen–Stockmeyer: alternating space s is within deterministic time 2^O(s)"
  topic := "space complexity"
  sources := [
    { paper := ChandraKozenStockmeyer1981, theorem := unverified, locator := "Section 3" },
    { paper := Sipser2013, theorem := unverified, locator := "Section 10.3" }
  ]
  theorems := [
    Turing.MultiTapeATM.RecognizesInSpace.mem_DTIME,
    Cslib.Complexity.exists_mem_DTIME_of_mem_ASPACE,
    Cslib.Complexity.exists_mem_DTIME_of_mem_ASPACE_of_log2_le
  ]
  scope := "One finite-state alternating multi-tape machine per problem with least-fixed-point \
    acceptance and work space s(n) (RecognizesInSpace.mem_DTIME, branches need not halt) or \
    c₁·s(n) + c₂ with every branch halting (ASPACE) along every computation prefix; DTIME is \
    deterministic decision within c₁·2^(c·(log₂ n + s(n) + 1)) + c₂ steps, or 2^(c·s(n)) when \
    log₂ n ≤ s(n); no constructibility hypothesis; the converse inclusion is not included; \
    arbitrary injective encodings."

register_result "nspace-dtime" where
  title := "Nondeterministic space s is within deterministic time 2^O(s)"
  topic := "space complexity"
  sources := [
    { paper := AroraBarak09, theorem := unverified, locator := "Section 4.1" },
    { paper := Sipser2013, theorem := unverified, locator := "Section 8.4" }
  ]
  theorems := [
    Cslib.Complexity.exists_mem_DTIME_of_mem_NSPACE,
    Cslib.Complexity.exists_mem_DTIME_of_mem_NSPACE_of_log2_le,
    Turing.MultiTapeNTM.RecognizesInSpace.mem_DTIME
  ]
  scope := "One finite-state binary nondeterministic multi-tape machine per problem with \
    work space c₁·s(n) + c₂ along every computation prefix; the recognizer form permits \
    nonterminating branches. DTIME is deterministic decision within \
    c₁·2^(c·(log₂ n + s(n) + 1)) + c₂ steps, or 2^(c·s(n)) when log₂ n ≤ s(n); no \
    constructibility hypothesis, unlike the source's space-constructible S; arbitrary \
    injective encodings."

register_result "reingold" where
  title := "Reingold: undirected reachability is in L"
  topic := "space complexity"
  sources := [
    { paper := Reingold2008, theorem := unverified, locator := unverified },
    { paper := AroraBarak09, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.USTCON_mem_L
  ]
  scope := "Simple undirected graphs encoded by a unary header 1^n 0 1^s 0 1^t 0 and the \
    row-major adjacency matrix (encUSTCON). One native machine halts on and decides every \
    encoded instance of length L within c·(⌊log₂ L⌋ + 1) work cells; malformed inputs are \
    unconstrained. The reduction-defined SL = L corollary is not part of this entry."

register_result "bipartite-in-logspace" where
  title := "Non-bipartiteness is log-space many-one equivalent to undirected connectivity; \
    bipartiteness is in L"
  topic := "space complexity"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Exercise 5.16",
      locator := "January 2007 r2.pdf, printed p. 196; PDF p. 80" }
  ]
  theorems := [
    Cslib.Complexity.Bipartite.compl_logSpaceReducible_USTCON,
    Cslib.Complexity.Bipartite.logSpaceReducible_compl_USTCON,
    Cslib.Complexity.Bipartite.USTCON_logSpaceReducible_compl,
    Cslib.Complexity.Bipartite.mem_L
  ]
  scope := "Undirected graphs as symmetric loopless adjacency matrices on Fin n, encoded by \
    encUGraph (a unary header 1^n 0 and the row-major matrix); bipartite means Mathlib's \
    SimpleGraph.IsBipartite. The equivalence is under native visited-cell logspace many-one \
    reductions, in the form non-bipartiteness ≤ USTCON (n disjoint copies of the guideline's \
    double cover, one USTCON query) and USTCON ≤ non-bipartiteness, the latter the trivial \
    reduction through USTCON ∈ L rather than the guideline's edge augmentation. Bipartiteness \
    ∈ L follows from Reingold's USTCON ∈ L and closure of L under complement."

register_result "bounded-stcon-in-nl" where
  title := "Length-bounded directed s–t connectivity is in NL"
  topic := "space complexity"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Exercise 5.19",
      locator := "January 2007 r2.pdf, printed p. 197; PDF p. 81" }
  ]
  theorems := [
    Cslib.Complexity.BoundedSTCON.mem_NL
  ]
  scope := "Directed adjacency-matrix graphs (encSTCON, framed) followed by a natural bound in \
    binary (encBoundedSTCON); walks of at most bound arcs, zero-length walks allowed. Negative \
    integer bounds are outside the encoding (they are always no-instances). Native visited-cell \
    NL. Outside-fleet six-point check on PR #6364."

register_result "undirected-distance-at-most-nl-complete" where
  title := "Undirected s–t paths of length at most K: NL-complete"
  topic := "space complexity"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Exercise 5.24 (at most)",
      locator := "January 2007 r2.pdf, printed p. 198; PDF p. 82" }
  ]
  theorems := [
    Cslib.Complexity.UDistanceAtMost.logSpaceComplete
  ]
  scope := "The literal 'at most K' question. Undirected graphs as symmetric loopless adjacency \
    matrices with terminals (encUSTCON), framed and followed by the natural bound K in binary \
    (encUDistance); the language is edist s t ≤ K, equivalently a path of at most K edges. \
    Native visited-cell NL and logspace many-one reductions; hardness uses the guideline's \
    layered graph with n + 1 layers and bound n. Outside-fleet six-point check on PR #6364."

register_result "undirected-shortest-distance-nl-complete" where
  title := "Undirected s–t distance exactly K: NL-complete (shortest-distance reading)"
  topic := "space complexity"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Exercise 5.24 (exactly), interpreted",
      locator := "January 2007 r2.pdf, printed p. 198; PDF p. 82" }
  ]
  theorems := [
    Cslib.Complexity.UDistanceEq.logSpaceComplete
  ]
  scope := "An interpretation, not the literal question: 'a path of length exactly K' is read \
    as 'the distance is K' (edist s t = K), following the exercise title, its NL = coNL \
    guideline and Exercise 5.27. The literal question differs: a triangle with adjacent \
    terminals has a simple path of exactly 2 edges but distance 1. Same encoding and classes \
    as the 'at most' entry; disconnected pairs are in neither language. Outside-fleet \
    six-point check on PR #6364."


register_result "uconn-in-logspace" where
  title := "Undirected connectivity of a whole graph is in L"
  topic := "space complexity"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Theorem 5.6",
      locator := "January 2007 r2.pdf, printed p. 170; PDF p. 54" }
  ]
  theorems := [
    Cslib.Complexity.UCONN.logSpaceReducible_USTCON,
    Cslib.Complexity.UCONN_mem_L
  ]
  scope := "Undirected graphs as symmetric loopless adjacency matrices on Fin n, encoded by \
    encUGraph (a unary header 1^n 0 and the row-major matrix). Connected means a path between \
    every pair of vertices (Appendix G.1), formalized as SimpleGraph.Preconnected, so the graph \
    with no vertices is connected. Native visited-cell L. The proof is a logspace many-one \
    reduction to USTCON (n copies of the graph in series, one query) and Reingold's USTCON ∈ L, \
    not the draft's direct expander transformation (Claims 5.7, 5.9 and Lemma 5.10 are \
    separate)."

register_result "strongly-connected-nl-complete" where
  title := "Strongly connected digraphs are NL-complete"
  topic := "space complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 4, Exercise 4",
      locator := "Web draft 2007-01-08, printed p. 89; PDF p. 105" },
    { paper := Goldreich2007DraftR2, theorem := "Exercise 5.23",
      locator := "January 2007 r2.pdf, printed p. 198; PDF p. 82" }
  ]
  theorems := [Cslib.Complexity.StronglyConnected.logSpaceComplete]
  scope := "Digraphs on Fin n with loops allowed, encoded by encDigraph: a unary header 1^n 0 \
    and the row-major adjacency matrix (the encSTCON layout without s and t); the empty digraph \
    is strongly connected. Native visited-cell NL: membership by one nondeterministic counter \
    program that guesses a path for every ordered pair, every branch halting; hardness by a \
    native logspace many-one reduction from STCON adding arcs v → s and t → v. Completeness for \
    the draft's ever-non-blank space class needs the measure bridge of draft Theorem 4.16."

register_result "primes" where
  title := "Agrawal–Kayal–Saxena: PRIMES is in P"
  topic := "algorithms"
  sources := [
    { paper := AKS2004, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.primes_mem_P
  ]
  scope := "Naturals in binary, least significant digit first (encNat); native multi-tape P \
    with polynomial time and space. The decider is the AKS algorithm with integer thresholds \
    on the word RAM, simulated by a Turing machine; no exponent is stated."

register_result "immerman-szelepcsenyi" where
  title := "Immerman–Szelepcsényi: nondeterministic space is closed under complement"
  topic := "space complexity"
  sources := [
    { paper := Immerman1988, theorem := unverified, locator := unverified },
    { paper := Szelepcsenyi1987, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.NSPACE_eq_coNSPACE
  ]
  scope := "NSPACE(s) = coNSPACE(s) for every s with log₂ n ≤ s(n); no constructibility \
    assumed. One finite-state native machine per problem, work space c₁·s(n) + c₂ along every \
    computation prefix, every branch terminating, arbitrary injective encodings."

register_result "immerman-szelepcsenyi-nl" where
  title := "Immerman–Szelepcsényi: NL equals coNL"
  topic := "space complexity"
  sources := [
    { paper := Immerman1988, theorem := unverified, locator := unverified },
    { paper := Szelepcsenyi1987, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.NL_eq_coNL
  ]
  scope := "NL = coNL for the native class NL (one finite-state machine, work space \
    c·(⌊log₂ n⌋ + 1) along every computation prefix, every branch halting) and arbitrary \
    injective encodings: the case s = log₂ of the nondeterministic-space theorem."

register_result "shamir" where
  title := "Shamir: IP equals PSPACE"
  topic := "interactive proofs"
  sources := [
    { paper := Shamir1992, theorem := unverified, locator := unverified },
    { paper := Shen1992, theorem := unverified, locator := unverified },
    { paper := LundFortnowKarloffNisan1992, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.IP_eq_PSPACE
  ]
  scope := "IP with private fair coins: one oracle-machine verifier under a strict polynomial \
    clock, completeness 2/3 and soundness 1/3 quantified over every stateful prover; PSPACE is \
    decided by one deterministic machine in polynomial space; arbitrary injective encodings."

register_result "dip-eq-np" where
  title := "Deterministic interactive proofs decide exactly NP"
  topic := "interactive proofs"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 8.3",
      locator := "web draft 2007-01-08, Section 8.1 (printed p. 148, PDF p. 164)" }
  ]
  theorems := [Cslib.Complexity.dIP_eq_NP]
  scope := "dIP is the coin-free case of the IP model: a deterministic word-query verifier run \
    against every randomized stateful prover, strict oracle PPT (one machine, one polynomial \
    clock), completeness 1 and soundness 0; arbitrary injective encodings."

register_result "arora-barak-oracle-counterexample-to-3sat" where
  title := "Some language in relativized NP has no oracle-aided polynomial-time reduction to 3SAT"
  topic := "relativization"
  sources := [
    { paper := AroraBarak07, theorem := "Exercise 3 §6",
      locator := "January 2007 draft, printed p. 74; PDF p. 90" }
  ]
  theorems := [Cslib.Complexity.exists_unaryLengthLanguage_not_reducibleWithOracle]
  scope := "For every fixed encoded target, an oracle B has a unary length language in NP \
    relative to B with no many-one reduction computable in polynomial time with access to B. \
    The 3SAT client in CslibFrontierTests/Relativization.lean takes the fixed target \
    encCNF '' ThreeSAT with the identity encoding of words. The disallowed reductions can \
    output any word, including malformed CNF codes on negative inputs. The witness language \
    asks whether its unary input length occurs among words in B. The diagonal test checks \
    the encoded target after the candidate has finished its queries. Outside-fleet source \
    check: https://github.com/cslib-community/cslib-frontier/pull/6463#pullrequestreview-5958790305"

register_result "arora-barak-perfectly-complete-set-lower-bound" where
  title := "A perfectly complete AM protocol for set lower bounds"
  topic := "interactive proofs"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 8, Exercise 3",
      locator := "web draft 2007-01-08, printed p. 166, PDF p. 182; protocol in Section 8.4.1, \
        printed p. 152" }
  ]
  theorems := [Cslib.Complexity.exists_perfectlyComplete_verifier_of_card_certifiedSet]
  scope := "Outside check: PR #6400, review 5953960536. One polynomial-time public-coin \
    two-message verifier (Arthur's random string, then Merlin's reply) for the whole input \
    family: with S_a the strings of N(n) bits having a c(n)-bit certificate accepted by a \
    polynomial-time test and K a polynomial-time positive threshold in binary, every random \
    string has an accepted reply when K(a) ≤ |S_a|, and at least two thirds have none when \
    2|S_a| ≤ K(a); inputs in between carry no obligation. Proved via amplification, \
    Lautemann's shifts and two parallel trials, not via the hint's prover-chosen hash \
    functions and Cartesian powers; arbitrary injective encodings."

register_result "perfect-soundness-ip-subset-np" where
  title := "Interactive proofs with perfect soundness are in NP"
  topic := "interactive proofs"
  sources := [
    { paper := Goldreich2007DraftR5, theorem := "Proposition 9.2",
      locator := "April 2007 draft r5.pdf, PDF p. 9; printed p. 391" }
  ]
  theorems := [Cslib.Complexity.IsInteractiveProof.mem_NP,
    Cslib.Complexity.mem_NP_of_exists_pos_acceptProb]
  scope := "Perfect soundness gives NP for every strict oracle-PPT IP verifier with any \
    positive completeness; the source's perfect-completeness assumption is dropped. The \
    certificate is a transcript of at most t messages and replies of at most t bits with the \
    t coins, t the clock; arbitrary injective encodings."

register_result "toda" where
  title := "Toda: a counting oracle decides the polynomial hierarchy"
  topic := "counting classes"
  sources := [
    { paper := Toda1991, theorem := unverified, locator := unverified },
    { paper := AroraBarak09, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.PH_subset_PWithSharpPOracle
  ]
  scope := "PH ⊆ P^#P, where P^#P is one polynomial-time oracle program that is correct against \
    every oracle language answering the bits of some #P function (explicit witness counts). \
    The class does not count queries; the construction asks a single one. PH uses \
    polynomial-time alternating verifiers; arbitrary injective encodings."

register_result "sharp-cycle-fp-p-eq-np" where
  title := "If #CYCLE is in FP then P = NP"
  topic := "counting classes"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 9.4",
      locator := "Web draft 2007-01-08, §9.1, printed p. 173; PDF p. 189" }
  ]
  theorems := [
    Cslib.Complexity.P_eq_NP_of_computableInPolyTime_SharpCycle,
    Cslib.Complexity.SharpCycle.mem_DirHamCycle_iff
  ]
  scope := "#CYCLE counts the simple directed cycles (Cycle values: nonempty, no repeated \
    vertex, declared vertices, arcs of the edge list; a self-loop is a cycle of length one) of \
    a graph under encGraph. FP is native polynomial-time computability with binary output \
    encNat. The gadget reduction uses n*n+n+3 layers and threshold 2^(m*n) instead of the \
    draft's n log n + 1 and n^(n^2). P = NP holds for every injective encoding."

register_result "bqp-pp" where
  title := "Adleman–DeMarrais–Huang: BQP is contained in PP"
  topic := "quantum complexity"
  sources := [
    { paper := AdlemanDeMarraisHuang1997, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.BQP_subset_PP
  ]
  scope := "BQP: bounded-error (2/3 versus 1/3) polynomial-time uniform families of circuits \
    over the fixed gate set {Hadamard, NOT, CNOT, Toffoli}, generated from n in unary, \
    accepting by measuring qubit 0 from the zero-padded input; PP is native multi-tape strict \
    majority over certificates. Equivalence to textbook BQP over arbitrary elementary gates \
    (universality, Solovay–Kitaev) is not formalized."

register_result "barrington" where
  title := "Barrington: five states capture NC¹"
  topic := "circuit complexity"
  sources := [
    { paper := Barrington1989, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Boolean.NC_one_eq_polyLength_perm_five
  ]
  scope := "Class equality for languages over Bool: nonuniform polynomial-size De Morgan \
    circuits of depth O(log n + 1), every gate counted, versus polynomial-length permutation \
    programs over S₅ with length-dependent acceptance sets. No uniform generator or compiler \
    runtime is asserted."

register_result "constant-depth" where
  title := "Håstad: parity resists shallow circuits"
  topic := "circuit complexity"
  sources := [
    { paper := Hastad1986, theorem := unverified, locator := unverified },
    { paper := Jukna2012, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity_of_depthWith_le
  ]
  scope := "A circuit of NOT and unbounded fan-in AND/OR gates of AND/OR depth at most d \
    (negations free in depth) computing parity of n bits has at least 2^s gates whenever \
    s ≥ 2 and 17s(16s + 1)^(d - 2) ≤ n (truncated subtraction); size counts every gate, \
    including NOT and constants. Explicit finite bound with the sharp exponent 1/(d - 1); \
    nonuniform."

register_result "constant-depth-mod-p" where
  title := "Razborov–Smolensky: parity resists shallow circuits with MOD p gates"
  topic := "circuit complexity"
  sources := [
    { paper := Razborov1987, theorem := unverified, locator := unverified },
    { paper := Smolensky1987, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Boolean.Smolensky.two_mul_two_pow_le_size_of_computes_parity
  ]
  scope := "For an odd prime p, a circuit of NOT, unbounded fan-in AND/OR and MOD_p gates (true \
    when the number of true inputs is nonzero mod p) of depth d computing parity of n bits \
    satisfies 2·2^ℓ ≤ 5·size whenever ℓ ≥ 1 and 100(((p - 1)ℓ)^d + 1)² ≤ n + 1. Depth and \
    size count every gate, including NOT and constants; nonuniform."

register_result "middle-slice-lower-bound-mod-two" where
  title := "Razborov's rank method: a middle slice is not in AC⁰[2]"
  topic := "circuit complexity"
  sources := [
    { paper := Razborov1987, theorem := unverified, locator := unverified },
    { paper := RazborovRudich1997, theorem := unverified, locator := "Section 3.2, p. 27" },
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016, theorem := unverified,
      locator := "p. 10:20" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.Razborov.middleSlice_notMem_AC0Mod_two
  ]
  scope := "No family of circuits of NOT, unbounded fan-in AND/OR and MOD_2 gates of constant \
    depth and polynomial size decides the language of bit strings of length n with exactly \
    ⌈n/2⌉ - ⌊√(n + 1)/10⌋ zeros (nonuniform). Proved through a variant of Razborov's GF(2) \
    rank property (one square matrix, threshold C(n, a)/2). Razborov and Rudich (Section 3.2) \
    state the property only abstractly; the explicit p = 2 form is the sketch of Carmosino et \
    al. (p. 10:20). Razborov's original paper was not checked for its hard function. \
    Membership in P and the separation are middle-slice-mod-two."

register_result "middle-slice-mod-two" where
  title := "Razborov's rank method: a middle slice is in P but not in AC⁰[2]"
  topic := "circuit complexity"
  sources := [
    { paper := Razborov1987, theorem := unverified, locator := unverified },
    { paper := RazborovRudich1997, theorem := unverified, locator := "Section 3.2, p. 27" },
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016, theorem := unverified,
      locator := "p. 10:20" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.Razborov.middleSlice_mem_P,
    Cslib.Circuits.Boolean.Razborov.exists_mem_P_notMem_AC0Mod_two
  ]
  scope := "The language of bit strings of length n with exactly ⌈n/2⌉ - ⌊√(n + 1)/10⌋ zeros is \
    decided in polynomial time by a multi-tape Turing machine and is not in AC⁰[2]: no family of \
    circuits of NOT, unbounded fan-in AND/OR and MOD_2 gates of constant depth and polynomial \
    size decides it (nonuniform). Proved through a variant of Razborov's GF(2) rank property \
    (one square matrix, threshold C(n, a)/2); the sources give the abstract property and a \
    sketch, and Razborov's original paper was not checked for its hard function. The lower bound \
    itself is the separate entry middle-slice-lower-bound-mod-two."

register_result "rank-property-natural-ac0-2" where
  title := "Razborov's rank property is a P/poly-natural property useful against AC⁰[2]"
  topic := "circuit complexity"
  sources := [
    { paper := RazborovRudich1997, theorem := unverified, locator := "Section 3.2, p. 27" },
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016, theorem := "Theorem 5.3",
      locator := "p. 10:19; p = 2 property p. 10:20" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.Razborov.isNatural_PPoly_and_isUseful_AC0Mod_two_rankProperty,
    Cslib.Circuits.Boolean.Razborov.isUseful_AC0Mod_two_rankProperty,
    Cslib.Circuits.Boolean.Razborov.notMem_rankProperty_rankLength_of_computes,
    Cslib.Circuits.Boolean.Razborov.rankLength_add_one_le
  ]
  scope := "Along the level ⌈n/2⌉ - ⌊√(n + 1)/10⌋, the GF(2) rank property (a variant: one square \
    matrix, threshold C(n, a)/2) is large, its truth tables are decided by De Morgan circuits of \
    173·8^n gates (P/poly; size only, depth not certified, not the sources' NC²), and it is useful \
    against AC⁰[2] (NOT, unbounded fan-in AND/OR and MOD_2 gates; nonuniform). Explicitly, at \
    the input length m = rankLength d x, which satisfies m + 1 ≤ 401·2^(2d(2d+7))·x^(2d) for \
    x ≥ 1, no circuit of depth at most d with at most 2^x gates computes a function with the \
    property. p = 2 only; the constants are this library's. \
    The learning consequence for p = 2 is the separate entry cikk-learning-ac0-2."

register_result "braverman" where
  title := "Braverman: polylogarithmic independence fools AC⁰"
  topic := "circuit complexity"
  sources := [
    { paper := Braverman2010, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Boolean.Braverman.fools_of_isKWiseIndependent
  ]
  scope := "A circuit of NOT and unbounded fan-in AND/OR gates of depth at most d, with at most \
    2^q gates, each of fan-in below 2^q (q ≥ 1), is fooled with error 2^(-q) in expectation by \
    every k-wise independent distribution (vanishing biases on nonempty sets of at most k \
    coordinates) once k ≥ (64q)^((2d + 3)(d + 7) + 1). Our own constants and exponent, weaker \
    than Braverman's; size and depth count NOT gates and constants; nonuniform and \
    information-theoretic."

register_result "majority-three-zero-error-expected-cost" where
  title := "Three-bit majority has exact zero-error expected query complexity 8/3"
  topic := "query complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Examples 11.14 and 11.18",
      locator := "Web draft 2007-01-08, printed pp. 215–216; PDF pp. 231–232" }
  ]
  theorems := [
    Cslib.QueryComplexity.zeroErrorComplexity_majority_three,
    Cslib.QueryComplexity.MajorityThree.algorithm_expectedCost,
    Cslib.QueryComplexity.MajorityThree.hardDistribution_lower,
    Cslib.QueryComplexity.MajorityThree.weights_hardDistribution
  ]
  scope := "Total majority on three Boolean coordinates. Existing finite-support zero-error \
    randomized-tree model; cost counts executed queries, including repeats. The uniform \
    six-order short-circuit algorithm has expected cost 2 on constants and 8/3 otherwise. \
    The uniform law on six nonconstant inputs forces cost at least 8/3 on all correct \
    adaptive deterministic trees, including arbitrary repeats. Local computation is free."

register_result "goldreich-majority-randomized-probes" where
  title := "Deciding majority requires linearly many randomized probes"
  topic := "query complexity"
  sources := [
    { paper := Goldreich2007DraftR5, theorem := "Exercise 10.8",
      locator := "April 2007 draft r5.pdf, PDF p. 116; printed p. 498" }
  ]
  theorems := [
    Cslib.RandomizedDecisionTree.Computes.exists_div_two_add_one_le_three_mul_cost_majority
  ]
  scope := "Outside check: PR #6397, review 5953955718. For n ≥ 1, every finitely supported \
    mixture of adaptive decision trees computing majority (at least ⌈n/2⌉ ones) on n bits \
    with error ≤ 1/3 on every input has an input x and a tree t it can draw with \
    ⌊n/2⌋ + 1 ≤ 3 · t.cost x, where cost counts executed probes, repeats included. The \
    strict convention follows the same way from blockSensitivity_threshold (checked client). \
    Proved via Nisan's block-sensitivity bound on executed queries and s(MAJ_n) = ⌊n/2⌋ + 1, \
    not via the guideline's statistical-distance bound."

register_result "yao-zero-error-expected-cost" where
  title := "Expected-cost Yao minimax with optimal algorithm and hardest input law"
  topic := "query complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 11.17; Definitions 11.13, 11.15–11.16",
      locator := "Web draft 2007-01-08, printed pp. 215–216; PDF pp. 231–232" }
  ]
  theorems := [
    Cslib.QueryComplexity.zeroErrorComplexity_eq_iSup_distributionalExpectedComplexity,
    Cslib.QueryComplexity.exists_optimal_expectedCost,
    Cslib.QueryComplexity.exists_computes_distributionalCost_eq,
    Cslib.QueryComplexity.exists_distributionalExpectedComplexity_eq_zeroErrorComplexity
  ]
  scope := "Finite Boolean coordinate space, arbitrary output type, total everywhere-correct \
    deterministic trees and finitely supported randomized trees. Expected executed queries, \
    including repeated queries; free local computation. Numerical equality with the maximum \
    optimized distributional expected cost, both sides attained. No finite-output assumption, \
    no bounded-error depth substitution, no expected Turing-machine runtime claim."

register_result "adjacent-pair-sensitivity-separation" where
  title := "Adjacent-pair block functions: sensitivity Θ(√n), block sensitivity Θ(n)"
  topic := "query complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 11, Exercise 2",
      locator := "Web draft 2007-01-08, printed p. 218; PDF p. 234" }
  ]
  theorems := [Cslib.BitString.adjacentPairSqrt_measures]
  scope := "Every length n ≥ 4, with Nat.sqrt n balanced contiguous blocks of sizes \
    n / k + [i < n % k]; a block accepts exactly two adjacent true bits, overlapping choices \
    included. Native CSLib sensitivity, block sensitivity, certificate complexity and \
    decision-tree complexity: √n ≤ s ≤ 3√n (floor square root), n ≤ 3 bs and \
    bs ≤ C ≤ D ≤ n. No exact values (such as D = n) are claimed."

register_result "adjacent-pair-block-bounds" where
  title := "Adjacent-pair block functions with arbitrary block sizes: sensitivity and block \
    sensitivity bounds"
  topic := "query complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 11, Exercise 2 (general block layout)",
      locator := "Web draft 2007-01-08, printed p. 218; PDF p. 234" }
  ]
  theorems := [
    Cslib.BitString.sensitivity_adjacentPairBlocks_le,
    Cslib.BitString.sum_half_le_blockSensitivity_adjacentPairBlocks
  ]
  scope := "Unequal consecutive blocks covering n coordinates, each accepting exactly two \
    adjacent true bits: sensitivity is at most max(3k, M) for k blocks of at most M bits, and \
    the sum over blocks of half their sizes (rounded down) is at most the block sensitivity."

register_result "boolean-two-element-arithmetic-simulation" where
  title := "Boolean and two-element arithmetic circuits have linearly related sizes"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 14, Exercise 1 (two-element case)",
      locator := "Web draft 2007-01-08, printed p. 265; PDF p. 281" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.exists_arithmetic_simulation,
    Cslib.Circuits.Boolean.exists_boolean_simulation
  ]
  scope := "Bool's Boolean ring, with XOR addition and AND multiplication. All outputs and \
    all inputs are preserved; arithmetic simulates De Morgan circuits with size factor 3, \
    and De Morgan circuits simulate arithmetic with factor 4. Constants count as gates; \
    input/output wires are free. Nonuniform existence, not compiler runtime or formal \
    polynomial equality. This does not complete the arbitrary fixed finite-field exercise."

register_result "von-neumann-fair-bit-extraction" where
  title := "Von Neumann extraction: an exact fair bit from a biased coin"
  topic := "randomized complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Lemma 7.15",
      locator := "Web draft 2007-01-08, §7.4, printed p. 124; PDF p. 140" }
  ]
  theorems := [Cslib.Probability.DDGTree.vonNeumann_generatesWith_coin,
    Cslib.Probability.DDGTree.expectedFlipsWith_coin_vonNeumann,
    Cslib.Probability.DDGTree.exists_generatesWith_coin_iff]
  scope := "Unbounded coin-reading trees (DDG trees) run on independent flips of a coin of \
    bias 0 < rho < 1: exact fair output and exactly 1/(rho(1-rho)) expected flips. Some tree \
    outputs a fair bit iff 0 < rho < 1. Cost counts coin flips; no Turing-machine runtime."

register_result "biased-coin-from-fair-digits" where
  title := "A coin of any bias from fair coins with expected two flips"
  topic := "randomized complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Lemma 7.14",
      locator := "Web draft 2007-01-08, §7.4, printed p. 124; PDF p. 140" }
  ]
  theorems := [Cslib.Probability.DDGTree.coinOfDigits_spec_of_computableInPolyTime]
  scope := "Digit-comparison DDG tree for any binary expansion of rho in [0,1] (rho = 1 via \
    0.111...): exact coin of bias rho, exactly 2 expected fair bits. With digits polynomial-time \
    from the unary index, the expected sum of the digit machine's time bounds (plus one per \
    flip) is the finite series sum_n (t n + 1) 2^-n. The comparison loop is not compiled to a \
    Turing machine."

register_result "or-exact-degree" where
  title := "Polynomials computing OR on the cube have full degree"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 13, Exercise 6",
      locator := "Web draft 2007-01-08, printed p. 252; PDF p. 268" }
  ]
  theorems := [Cslib.BitString.card_le_totalDegree_of_eval_eq_or,
    Cslib.BitString.le_totalDegree_of_eval_eq_or_zmod,
    Cslib.BitString.totalDegree_orPoly]
  scope := "Every polynomial over a nontrivial commutative ring, multilinear or not, that \
    agrees with OR at the 0/1 points has total degree at least the number of variables; \
    1 - prod (1 - X_i) attains it. The GF(q) corollary is stated over ZMod q with q prime. \
    Exact representation only; no approximate-degree statement."

register_result "parity-nc-one" where
  title := "Parity is in NC¹"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 13, Exercise 7 (PARITY)",
      locator := "Web draft 2007-01-08, printed p. 253; PDF p. 269" }
  ]
  theorems := [Cslib.Circuits.Boolean.parity_mem_NC_one]
  scope := "Nonuniform NC¹: polynomial-size fan-in-two De Morgan circuit families of depth \
    O(log n), negations free. Proved by an explicit balanced XOR formula of depth \
    2 ceil(log2 n), not by the Karchmer–Wigderson game the exercise suggests."

register_result "formal-complexity-measure-leaf-bound" where
  title := "Formal complexity measures lower-bound constant-free formula leaf size"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 22.1",
      locator := "Web draft 2007-01-08, §22.1, printed p. 438; PDF p. 454" }
  ]
  theorems := [Cslib.Circuits.Boolean.FormalComplexityMeasure.le_leafSize]
  scope := "Natural-valued measures subadditive under AND/OR and at most one on each literal. \
    Constant-free De Morgan formulas, with arbitrary negations; input-leaf size. \
    No complement invariance. Constants are excluded because their library leaf cost is zero."

register_result "formal-complexity-measure-quarter-density" where
  title := "A large formal complexity measure is large on a quarter of truth tables"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Lemma 22.2",
      locator := "Web draft 2007-01-08, §22.1, printed p. 438; PDF p. 454" }
  ]
  theorems := [Cslib.Circuits.Boolean.FormalComplexityMeasure.card_le_four_mul_card]
  scope := "For any fixed arity including zero, if one function has measure at least c, \
    at least one quarter of all truth tables have measure at least c/4. \
    Natural-number cardinalities with denominators cleared; no computational claim. \
    Theorem 22.3's stronger near-total-density endpoint is not included."

register_result "integer-permanent-to-zero-one-permanent" where
  title := "The integer permanent reduces to the 0/1 permanent"
  topic := "counting complexity"
  sources := [
    { paper := Goldreich2007Draft, theorem := "Proposition 6.22",
      locator := "February 2007 draft r3.pdf, PDF p. 24; printed p. 226" }
  ]
  theorems := [
    Cslib.Complexity.intPermanent_eq_recoverPermanent_intTableToZeroOne,
    Cslib.Complexity.metricReducible_intPermanent_zeroOnePermanent,
    Cslib.Complexity.computableInPolyTime_intTableToZeroOne,
    Cslib.Complexity.computableInPolyTime_recoverPermanent,
    Cslib.Complexity.parsimoniousReducible_natPermanent_zeroOnePermanent
  ]
  scope := "Dense integer tables (encIntTable, binary sign-magnitude entries) read as n x n \
    matrices with missing entries 0, mapped by a native polynomial-time machine to dense 0/1 \
    tables (encBoolTable); the integer permanent is recovered in polynomial time from the input \
    and the 0/1 permanent. Entries are reduced modulo 2 n! S^n + 1 with S the sum of absolute \
    entries (Goldreich uses the maximum), then each residue is replaced by a binary chain of \
    relay vertices; the 0/1 dimension is n + 2 L n^2. One-query (metric) reduction, a special \
    case of the source's Cook reduction."

register_result "bpp-proper-subset-ppoly" where
  title := "BPP is strictly contained in P/poly on ordinary bit languages"
  topic := "circuit complexity"
  sources := [
    { paper := Goldreich2007Draft, theorem := "Theorem 6.3",
      locator := "February 2007 draft r3.pdf, PDF p. 9; printed p. 211" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.not_countable_PPoly,
    Cslib.Circuits.Boolean.exists_mem_PPoly_not_isDecidable,
    Cslib.Circuits.Boolean.BPP_ssubset_PPoly
  ]
  scope := "Ordinary bit languages with identity encoding encBits: nonuniform polynomial-size \
    De Morgan circuits strictly contain native seeded-verifier BPP. The witness has no native \
    machine decider and is obtained nonconstructively using P-selective sets/countability. \
    No efficient separator or uniform circuit-family construction. Strictness is not asserted \
    for arbitrary encoded finite instance domains, where the two classes coincide."

register_result "goldreich-coin-split-promise-corp" where
  title := "Splitting the coins of a very-low-error BPP algorithm gives a one-sided reduction \
    to promise-coRP"
  topic := "randomized complexity"
  sources := [
    { paper := Goldreich2007Draft, theorem := "Exercise 6.11",
      locator := "February 2007 draft r3.pdf, PDF p. 53; printed p. 255 (illustration in the \
        proof of Theorem 6.9: PDF p. 14; printed p. 216)" }
  ]
  theorems := [
    Cslib.Complexity.PromiseProblem.half_lt_toOuterMeasure_coinSplit_yes,
    Cslib.Complexity.PromiseProblem.rpReducibleWithError_coinSplit,
    Cslib.Complexity.PromiseProblem.coinSplit_mem_PromiseCoRP
  ]
  scope := "Instances x of any encoded type, |x| = (encA x).length; A' is a function of the \
    instance and the coin string, polynomial-time on encPair encA encBits for item 2, with \
    error below 2^-(p'(|x|)+1) over 2 p'(|x|) coins, stated by counting. Item 1 is \
    the explicit sampler hits Pi'_yes with probability > 1/2 on members of S \
    (half_lt_toOuterMeasure_coinSplit_yes), giving RPReducibleWithError with threshold 1/2 \
    between the complements (the RP orientation). Only the illustrative route, not Theorem 6.9. \
    Outside-fleet six-point source check: review 5951585789 on PR #6380."

register_result "arora-barak-ma-eq-np-of-hardness" where
  title := "Average-case hardness in E gives MA = NP"
  topic := "derandomization"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 16, Exercise 4",
      locator := "January 8, 2007 draft; printed 318 / PDF 334; Definition 16.7 printed 286 / \
        PDF 302" }
  ]
  theorems := [Cslib.Complexity.MA_eq_NP_of_isAverageCaseHard]
  scope := "Outside check: PR #6276, review 5947521916. MA enc = NP enc for every injective \
    instance encoding, assuming L ∈ E encBits whose slices are eventually IsAverageCaseHard \
    (non-strict, De Morgan gates counted, inputs not) for size 2^⌊n/c⌋, some natural c > 0. \
    The draft's hypothesis (f ∈ E, strict H_avg(f)(n) ≥ 2^(εn) for every n, Definition 6.1 \
    counting all nodes) implies this for every natural c > 1/ε: a De Morgan circuit with s \
    gates on n ≥ 1 inputs becomes a source circuit with O(n + s + 1) nodes and the output as \
    its only sink (prune unused gates, constants as x1 ∧ ¬x1 or its negation, unused inputs \
    folded into a dummy zero ORed into the output), which is at most 2^(εn) ≤ S for all \
    large n, and 1/2 + 1/S ≤ 1/2 + 1/s. MA has two-sided error 1/3."

register_result "one-bit-advice-undecidable" where
  title := "One bit of advice decides a length-dependent undecidable bit language"
  topic := "complexity theory"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Theorem 3.7 (one-bit undecidability endpoint)",
      locator := "January 2007 draft r2.pdf, PDF p. 6; printed p. 122" }
  ]
  theorems := [
    Cslib.Complexity.length_preimage_mem_PWithAdvice_one,
    Cslib.Complexity.exists_mem_PWithAdvice_one_not_isDecidable
  ]
  scope := "Native polynomial-time decider on framed advice/input pairs, with exactly one \
    arbitrary advice bit per input length. Some accepted bit language has no native machine \
    decider and has the same membership for all words of equal length. Advice need not be \
    computable; no efficient construction of the undecidable advice family is claimed. \
    Arbitrary advice hierarchies and strict P/1 versus P/poly remain separate."

register_result "sat-decidable-envelope-sparse-difference" where
  title := "SAT reductions into a decidable envelope with sparse difference imply SAT in P"
  topic := "complexity theory"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Exercise 3.12",
      locator := "January 2007 draft r2.pdf, PDF pp. 19–20; printed pp. 135–136" }
  ]
  theorems := [Cslib.Complexity.SAT_mem_P_of_sparse_diff]
  scope := "Native polynomial-time many-one SAT reduction to S under an explicit target \
    encoding; S is contained in a set G in P, and G minus S is sparse in prefix-census form. \
    Concludes SAT in P. G need not be sparse and S need not be decidable. Reuses Fortune \
    through a guarded UNSAT reduction; does not implement the source DFS proof."

register_result "boolean-ring-arithmetic-simulation" where
  title := "Boolean circuits simulated over any ring with size factor five"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 14, Exercise 1 (Boolean-to-arithmetic direction)",
      locator := "Web draft 2007-01-08, printed p. 265; PDF p. 281" }
  ]
  theorems := [Cslib.Circuits.Boolean.exists_ring_simulation]
  scope := "Any De Morgan circuit has an arithmetic circuit over any ring with at most \
    five times its gate count, preserving all outputs on zero/one-represented Boolean inputs. \
    Arithmetic uses constant/addition/multiplication gates; constants count and wires are free. \
    The zero/one representation is injective for nontrivial rings. No arbitrary ring-input \
    agreement, reverse simulation, formal polynomial identity or compiler-runtime claim."

register_result "arithmetic-bit-synthesis-injective-encoding" where
  title := "Arithmetic bit-synthesis with injective fixed-width encodings"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 14, Exercise 1 (synthesis-direction milestone)",
      locator := "Web draft 2007-01-08, printed p. 265; PDF p. 281" }
  ]
  theorems := [Cslib.Circuits.Synthesis.bitBlast_arithmetic]
  scope := "Arithmetic circuits on a semiring with supplied w-bit encoding and total decoder \
    satisfying a left-inverse law. Given already-available encoded input functions, all output \
    bits cost at most size * bitBlastCost w additional De Morgan gates. The encoding need not \
    be surjective, admitting odd fields. No free-input compiler, reverse simulation, encoding \
    construction or runtime claim; the full finite-field exercise remains open."

register_result "encoded-circuit-boolean-simulation" where
  title := "Boolean circuits for left-invertibly encoded bounded-arity computations"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 14, Exercise 1 (forward circuit milestone)",
      locator := "Web draft 2007-01-08, printed p. 265; PDF p. 281" }
  ]
  theorems := [Cslib.Circuits.Circuit.exists_encoded_boolean]
  scope := "Any interpreted circuit of arity at most two, with a supplied w-bit encoding and \
    decoder left inverse, has a Boolean circuit on N*w free inputs with M*w outputs, costing \
    at most size * bitBlastCost w gates. Correctness holds on valid encoded inputs, packed \
    wire-major by blocksEquiv.symm. Constants count as gates and wiring is free. No encoding \
    construction, reverse general-field simulation or compiler-runtime claim."

register_result "exact-advice-strict-hierarchy" where
  title := "Strict exact-advice hierarchy"
  topic := "complexity theory"
  sources := [
    { paper := Goldreich2007DraftR2,
      theorem := "Theorem 3.7; Exercise 3.3 / Theorem 4.1 with positive gap and capacity",
      locator := "January 2007 r2.pdf, PDF pp. 6, 16, 22; printed pp. 122, 132, 138" },
    { paper := GoldreichAdviceHierarchyAddendum,
      theorem := "Revised Theorem 4.1, positive one-bit difference",
      locator := "Online addendum, theorem and exact/no-exception technical note" }
  ]
  theorems := [
    Cslib.Complexity.PWithAdvice_ssubset_of_lt,
    Cslib.Complexity.PWithAdvice_pred_ssubset,
    Cslib.Complexity.PWithAdvice_const_ssubset_succ
  ]
  scope := "Strict pointwise growth and eventual upper truth-table capacity give strict \
    containment of exact-advice classes, with arbitrary noncomputable bounds/advice and a \
    native complete-pair polynomial clock. Includes positive predecessor, every constant \
    advice hierarchy. Does not prove the displayed hierarchy without positivity, or a \
    separation allowing finitely many errors."

register_result "constant-advice-strict-subset-ppoly" where
  title := "Every constant advice class is strictly smaller than P/poly"
  topic := "complexity theory"
  sources := [
    { paper := Goldreich2007DraftR2,
      theorem := "Theorem 3.7, strictness in the following paragraph",
      locator := "January 2007 r2.pdf, PDF p. 6; printed p. 122" }
  ]
  theorems := [Cslib.Circuits.Boolean.PWithAdvice_const_ssubset_PPoly]
  scope := "Every constant exact-advice class, including P/1, is strictly contained in \
    P/poly on bit languages. Uses the native full-pair polynomial-time advice class and \
    its existing polynomial-advice/circuit bridge; no uniform advice is claimed."

register_result "finite-carrier-boolean-simulation" where
  title := "Constant-factor Boolean simulation over every finite nonempty carrier"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 14, Exercise 1 (arithmetic-to-Boolean direction)",
      locator := "Web draft 2007-01-08, printed p. 265; PDF p. 281" }
  ]
  theorems := [Cslib.Circuits.Circuit.exists_finite_boolean]
  scope := "Any arity-at-most-two interpreted circuit over finite nonempty F is simulated \
    on valid encoded inputs by a Boolean circuit with all outputs and at most \
    size * bitBlastCost (Nat.clog 2 (Fintype.card F)) gates. The fixed encoding \
    fintypeEncoding uses a finite enumeration and least-significant-bit-first indexBits. \
    Constants count; wiring is free. No supplied encoding hypothesis, reverse simulation, \
    formal polynomial identity or uniform runtime claim; the enumeration is noncomputable."

register_result "exact-advice-length-comparison-qualification" where
  title := "Unbounded nonnegative gaps do not imply exact-advice containment"
  topic := "complexity theory"
  sources := [
    { paper := Goldreich2007DraftR2,
      theorem := "Exercise 3.3 / Theorem 4.1 (model qualification)",
      locator := "January 2007 r2.pdf, PDF pp. 16, 22; printed pp. 132, 138" },
    { paper := GoldreichAdviceHierarchyAddendum,
      theorem := "Theorem 4.1 revised (fixed-gap contrast, not refuted)",
      locator := "Online addendum, theorem and proof after the December 2014 discussion" }
  ]
  theorems := [
    Cslib.Complexity.PWithAdvice_subset_of_lt,
    Cslib.Complexity.PWithAdvice_subset_succ,
    Cslib.Complexity.exists_nonmonotone_advice_bounds
  ]
  scope := "Original counterexample for arbitrary exact-length advice: polynomial lower/gap \
    bounds, both draft capacity bounds and an unbounded nonnegative gap do not force class \
    containment. No computability of bounds/advice is claimed. Strict pointwise growth does \
    preserve inclusion by delimiter padding. This qualifies a reading of the displayed draft \
    hypotheses; it neither refutes nor completes positive-gap or official fixed-gap hierarchy \
    theorems."

register_result "sensitivity-relevant-coordinates" where
  title := "All-relevant Boolean functions have logarithmic maximum sensitivity"
  topic := "query complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 11, Exercise 1",
      locator := "Web draft 2007-01-08, printed p. 218; PDF p. 234" }
  ]
  theorems := [
    Cslib.BitString.card_relevant_le_sensitivity_mul_four_pow,
    Cslib.BitString.clog_le_three_mul_sensitivity_of_depends_on_all
  ]
  scope := "Total Boolean functions on n bits, using native maximum sensitivity. The number \
    of coordinates sensitive at some input is at most s(f)*4^s(f). If every coordinate is \
    relevant, Nat.clog 2 n ≤ 3*s(f), an explicit uniform logarithmic lower bound, including \
    the n=0 convention. Irrelevant coordinates are excluded from the cardinality theorem."

register_result "formula-bounds" where
  title := "Formula lower bounds: Khrapchenko's quadratic bound for parity"
  topic := "circuit complexity"
  sources := [
    { paper := Khrapchenko1971, theorem := unverified, locator := unverified },
    { paper := Jukna2012, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Boolean.sq_le_leafSize_of_computes_parity
  ]
  scope := "Every De Morgan formula computing parity of n bits has at least n² input leaves, \
    counted with multiplicity. Formula size only; no general-circuit lower bound."

register_result "formula-bounds-andreev" where
  title := "Formula lower bounds: Andreev's function"
  topic := "circuit complexity"
  sources := [
    { paper := Andreev1987, theorem := unverified, locator := unverified },
    { paper := Jukna2012, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Boolean.pow_two_mul_pow_three_le_formulaSize_andreev_sq
  ]
  scope := "Some B exists such that for all b ≥ B and m ≥ ⌊log₂ b⌋ + 2, the minimum De Morgan \
    formula leaf size L of Andreev's function on 2^b + b·m bits (explicit block indexing) \
    satisfies 2^(2b)·m³ ≤ 144·b²·(⌊log₂ b⌋ + 2)³·L². Finite quantitative bound; no \
    general-circuit lower bound."

register_result "constant-depth-arithmetic" where
  title := "Limaye–Srinivasan–Tavenas over any field (after Forbes): constant-depth algebraic \
    circuits for IMM need superpolynomial size"
  topic := "algebraic complexity"
  sources := [
    { paper := LimayeSrinivasanTavenas2021, theorem := unverified, locator := unverified },
    { paper := Forbes2024, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.SPCircuit.eventually_pow_lt_size_of_imm,
    Cslib.Circuits.Arithmetic.SPCircuit.two_rpow_le_of_imm
  ]
  scope := "Any field, formal polynomials, unbounded fan-in sum and product gates, product gates \
    reading distinct wires, size counting all gates. For constant product-depth Δ and every c, \
    for all large n, IMM of d = ⌊log₂ ⌊log₂ n⌋⌋ generic n × n matrices needs more than n^c \
    gates; the explicit form gives 2^(k(d^(1/(4^Δ - 1))/20 - 1/2)) ≤ \
    smCost(d)^Δ·(size + N + 1)^(2Δ + 1) when 10d ≤ k, 2^k ≤ n and Δ ≥ 1. Nonuniform."

register_result "cryptography" where
  title := "One-way functions yield pseudorandom generators"
  topic := "cryptography"
  sources := [
    { paper := HILL1999, theorem := unverified, locator := unverified },
    { paper := Holenstein2006, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Crypto.OneWay.exists_pseudorandomGenerator
  ]
  scope := "Every uniform one-way function on bit strings yields a deterministic polynomial-time \
    generator stretching every input by one bit, secure against uniform strict probabilistic \
    polynomial-time distinguishers with negligible advantage. Asymptotic security; no \
    optimized seed length; not a concrete implementation audit."

register_result "cryptography-prf" where
  title := "One-way functions yield adaptively secure pseudorandom functions"
  topic := "cryptography"
  sources := [
    { paper := GGM1986, theorem := unverified, locator := unverified },
    { paper := Holenstein2006, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Crypto.OneWay.exists_pseudorandomFunction
  ]
  scope := "Every uniform one-way function yields a length-preserving keyed family with a \
    deterministic polynomial-time evaluator, indistinguishable from a random function by \
    uniform adaptive oracle PPT adversaries with full stateful oracle semantics (negligible \
    advantage); via the one-way-to-PRG theorem and the GGM construction. Asymptotic security."

register_result "goldreich-levin-hard-core" where
  title := "Goldreich–Levin: every one-way function has a hard-core predicate, and one-way \
    permutations yield pseudorandom generators"
  topic := "cryptography"
  sources := [
    { paper := GoldreichLevin1989, theorem := unverified, locator := unverified },
    { paper := Goldreich2007DraftR4, theorem := "Theorem 7.7 and Proposition 8.9",
      locator := "March 2007 draft r4.pdf, PDF pp. 12 and 66; printed pp. 276 and 330" }
  ]
  theorems := [
    Cslib.Crypto.GoldreichLevin.padded_hardCore,
    Cslib.Crypto.OneWayPermutation.pseudorandomGenerator
  ]
  scope := "For every uniform one-way function f on bit strings, the inner product of the two \
    seed halves is hard-core for the padded function (x, r, s) ↦ (f x, r, s), with at most one \
    spare bit s so that every seed length is covered, against uniform strict PPT predictors \
    with negligible bias. This is not a hard-core predicate for f itself. For a length-preserving \
    one-way permutation, appending that bit gives a deterministic polynomial-time generator with \
    one-bit stretch, secure against uniform strict PPT distinguishers: Proposition 8.9 applied \
    to the padded function, which is then a length-preserving permutation, and its Theorem 7.7 \
    predicate. Asymptotic security; the source's explicit runtime and advantage trade-off is not \
    stated."

register_result "goldreich-stretch-amplification-last-bits" where
  title := "Stretch amplification of a one-bit pseudorandom generator by emitted last bits"
  topic := "pseudorandomness"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Proposition 8.8 (with Construction 8.7)",
      locator := "March 2007 draft r4.pdf, PDF p. 64; printed p. 328" }
  ]
  theorems := [
    Cslib.Crypto.PRGStretch.pseudorandomGenerator_take_forwardIterate,
    Cslib.Crypto.PRGStretch.take_forwardIterate_eq_flatten_emitBit
  ]
  scope := "Uniform PRGs as PseudorandomGenerator: a deterministic polynomial-time generator of \
    exact output length, secure against uniform PPT tests. The tests of prgRealGame and \
    prgIdealGame also receive the seed length n in unary, while those of Definition 8.1 \
    (Eq. (8.2)) see only the challenge word. On the one-bit premise a challenge-only test \
    recovers n = |word| - 1 and can simulate such a test, and on the conclusion a test may \
    ignore n, so the source implication follows even when the output length does not determine \
    the seed length. The stretch function ℓ is computable in polynomial time in unary and \
    satisfies n < ℓ n. The output is the sequence of last bits σ₁ ⋯ σ_ℓ of Construction 8.7, \
    identified with Eq. (8.8) by take_forwardIterate_eq_flatten_emitBit. Outside-fleet \
    six-point source check: review 5947783297 on PR #6287."

register_result "goldreich-exponential-time-design" where
  title := "An exponential-time set system with small pairwise intersections"
  topic := "pseudorandomness"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 8.19 (Condition 2 of Theorem 8.18)",
      locator := "March 2007 draft r4.pdf, PDF p. 110; printed p. 374" }
  ]
  theorems := [Cslib.Crypto.PRG.NisanWigderson.exists_computableInExpTime_design]
  scope := "For every real γ > 0: S(k, i) ⊆ [k] is given by a characteristic word of length k \
    (read by maskBlock), with |S(k, i)| = m(k) and |S(k, i) ∩ S(k, j)| ≤ γ m(k) for distinct \
    zero-based indices below ℓ(k), and m(k) ≥ c k and ℓ(k) ≥ 2 ^ (c k) for k ≥ k₀. The witness \
    is the deterministic greedy design with B = 10 q² + 1, q = max 2 ⌈1/γ⌉, t = ⌊k / B⌋, blocks \
    of q t elements, overlaps at most t and ℓ(k) = 2 ^ (t + 1) for k ≥ B (no blocks below B); \
    its size comes from a counting bound instead of the probabilistic method. Exponential time \
    is ComputableInExpTime in the parameter k on multi-tape machines, with k in unary and i in \
    binary: time O(2 ^ (δ k) (L + 1) ^ e). On the indices i < ℓ(k) the whole input has length \
    O(k + 1), so the time is 2 ^ O(k); the guideline's exponent 2 is a cost estimate for its \
    implementation. Outside-fleet six-point source check: review 5951520101 on PR #6378."

register_result "goldreich-low-degree-extension-individual-degree" where
  title := "Low-degree extensions of individual degree |H| - 1"
  topic := "codes"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 7.12",
      locator := "March 2007 draft r4.pdf, PDF p. 43; printed p. 307" }
  ]
  theorems := [Cslib.Code.exists_degreeOf_le_eval_eq_lowDegreeExtension]
  scope := "Any field F (the source's F is the finite field of its Theorem 7.12 construction) \
    and any finite H embedded in F. For every f : H^m → F there is an m-variate polynomial of \
    degree at most |H| - 1 in each variable that agrees with f on H^m; it is the Lagrange-basis \
    extension of the guideline. Uniqueness and the running time of footnote 12 are not \
    formalized."

register_result "goldreich-length-preserving-one-way" where
  title := "One-way functions yield length-preserving one-way functions"
  topic := "cryptography"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 7.1",
      locator := "March 2007 draft r4.pdf, PDF p. 41; printed p. 305" }
  ]
  theorems := [Cslib.Crypto.OneWay.exists_lengthPreserving]
  scope := "One-wayness as in Cslib.Crypto.OneWay (Definition 7.1): a uniform strict \
    probabilistic polynomial-time inverter receives the unary size and the image of a uniform \
    n-bit input, and any preimage counts. If f is one-way, some one-way f' satisfies \
    |f'(x)| = |x| for every x. The construction tags the image with the parameter and uses \
    self-delimiting padding instead of the guideline's 0 1^k padding; the statement is \
    unchanged. Outside-fleet six-point source check: review 5949710318 on PR #6352."

register_result "goldreich-weak-not-strong-one-way" where
  title := "If one-way functions exist, a weak one-way function need not be strongly one-way"
  topic := "cryptography"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 7.3",
      locator := "March 2007 draft r4.pdf, PDF p. 41; printed p. 305" }
  ]
  theorems := [Cslib.Crypto.OneWay.exists_weakOneWay_not_oneWay]
  scope := "If a one-way function exists, some weak one-way function is not strongly one-way. \
    Definitions 7.1 and 7.4 quantify over uniform strict PPT inverters receiving the unary \
    length and the image of a uniform input; any preimage counts. On the hard branch the \
    inverter for the tagged construction is called at length n + 1. On the easy branch the \
    identity inverter succeeds. The weak bound uses the constant polynomial 4. \
    Outside-fleet source check: review 5954074813 on PR #6412."

register_result "goldreich-circuit-agreement-limit" where
  title := "Small circuits agree with every function on 1/2 + t/2^n of the inputs"
  topic := "circuit complexity"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 7.10",
      locator := "March 2007 draft r4.pdf, PDF p. 42; printed p. 306" }
  ]
  theorems := [Cslib.Circuits.Boolean.exists_complexity_le_and_add_le_card_agree]
  scope := "Circuit complexity as in Cslib.Circuits.complexity, every gate counted; for every \
    f : {0,1}^n → {0,1} and every t with 2 t ≤ 2 ^ n, some function of complexity at most \
    t (2 n + 3) + 1 agrees with f on at least a 1/2 + t/2^n fraction of the inputs. For t = 1 \
    and n ≥ 1 this is the exercise's first claim, size 2 n + 4 with agreement 1/2 + 2^(-n)."

register_result "goldreich-no-universal-hard-core" where
  title := "If one-way functions exist, there is no universal hard-core predicate"
  topic := "cryptography"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 7.8",
      locator := "March 2007 draft r4.pdf, PDF p. 42; printed p. 306" }
  ]
  theorems := [Cslib.Crypto.OneWay.exists_oneWay_lastBit_eq]
  scope := "Given a one-way function f and a polynomial-time predicate b, the function g \
    that appends b(x) to f(x) is one-way. Its last bit is b(x) and is computable in \
    deterministic polynomial time from the image alone, as required by Definition 7.6. \
    The uniform strict PPT inverters receive the unary length and the image of a uniform \
    input, and any preimage counts. Outside-fleet source check: review 5954067975 on PR #6409."

register_result "random-functions-average-case-hard" where
  title := "Random functions are hard on average"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 16, Exercise 3",
      locator := "Web draft 2007-01-08; printed p. 318 / PDF p. 334 (Definition 16.7 on \
        p. 286 / PDF p. 302)" }
  ]
  theorems := [Cslib.Circuits.Boolean.exists_forall_complexity_le_card_agree_lt]
  scope := "For every n ≥ 400 some Boolean function f on n bits has H_avg(f)(n) ≥ 2^(n/10) in \
    the sense of Definition 16.7: for the natural number S = ⌈2^(n/10)⌉, every De Morgan \
    circuit with at most S gates (inputs not counted) agrees with f on fewer than a \
    1/2 + 1/S fraction of the inputs (strict, as in the draft). Outside-fleet source check: \
    PR #6269, pullrequestreview-5947274913."

register_result "naor-yung-uowhf" where
  title := "Naor–Yung: one-way permutations yield universal one-way hash functions"
  topic := "cryptography"
  sources := [
    { paper := NaorYung1989, theorem := unverified, locator := "Section 3" },
    { paper := Goldreich2004, theorem := unverified, locator := "Section 6.4.3.2" }
  ]
  theorems := [
    Cslib.Crypto.OneWayPermutation.targetCollisionResistant_naorYungHash,
    Cslib.Crypto.OneWayPermutation.exists_targetCollisionResistant_keyedHashFamily
  ]
  scope := "Every uniform one-way permutation f on bit strings gives a keyed hash family on all \
    bit strings, with polynomial-time keys, digests and evaluation, that is target \
    collision-resistant: a uniform strict PPT adversary that commits to a target before seeing \
    the key finds a distinct colliding input with negligible probability. Each compression step \
    uses a pivot-deletion quotient instead of the source's universal hash; a binary tree extends \
    the domain. Asymptotic security; no compact key-length bound."

register_result "inaccessible-entropy-from-owf" where
  title := "Inaccessible average max-entropy from one-way functions"
  topic := "cryptography"
  sources := [
    { paper := HHRVW2020, theorem := "Theorem 4.5", locator := "Section 4.2, p. 21" }
  ]
  theorems := [
    Cslib.Crypto.OneWay.rompelBase_logGap
  ]
  scope := "For a uniform one-way function g with fixed output length m(n), the uniform \
    polynomial-time function F₀(x, A, b, r) = (A, b, r, first min(r, n) bits of A g(x) + b, \
    zero-padded) has accessible average max-entropy against uniform strict PPT adversaries \
    eventually at most H(Z | F₀(Z)) - d log₂ n / n for every constant d > 0, witnessed at each d \
    by an adversary-independent accessible preimage set family. The construction deviates from \
    the source's F(x, g, i) = (g(f(x))₁..ᵢ, g, i) in three ways. The hash is the Boolean affine \
    family, whose n·m(n) + n-bit seed makes the input width n + (n·m(n) + n) + (⌊log₂ n⌋ + 1) = \
    Θ(n·m(n)), instead of the O(n) the source gets from O(n)-bit hash descriptions (its Theorem \
    5.2). The prefix length is min(r, n) for a uniform (⌊log₂ n⌋ + 1)-bit r, not uniform on [n]. \
    And g has a fixed output length rather than being length-preserving; an arbitrary one-way \
    function is first padded to such a g."

register_result "rompel-uowhf" where
  title := "Rompel: one-way functions yield universal one-way hash functions"
  topic := "cryptography"
  sources := [
    { paper := Rompel1990, theorem := unverified, locator := unverified },
    { paper := HHRVW2020, theorem := "Theorem 5.1", locator := "Section 5.1, p. 26" }
  ]
  theorems := [
    Cslib.Crypto.ShrinkingCollisionGrid.targetCollisionResistant_rompelHash,
    Cslib.Crypto.AdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantHash,
    Cslib.Crypto.OneWay.exists_targetCollisionResistant_keyedHashFamily
  ]
  scope := "Every uniform polynomial-time function family with inaccessible average max-entropy \
    against adversary-dependent accessible sets (Definition 3.9, \
    AdversaryInaccessibleEntropyFamily), and hence every uniform one-way function on bit strings, \
    gives a target collision-resistant keyed hash family on all bit strings against uniform \
    strict PPT adversaries that commit to a target before seeing the key. `rompelHash` is secure \
    for every shrinking collision grid. Each one-bit step takes a fresh subkey, so keys are \
    polynomial but not as compact as the source's O(|y| log t) bound. Asymptotic security."

register_result "resolution" where
  title := "Haken: pigeonhole formulas require long resolution proofs"
  topic := "proof complexity"
  sources := [
    { paper := Haken1985, theorem := unverified, locator := unverified },
    { paper := BeamePitassi1996, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.PL.CNF.two_pow_le_of_refutableInSize_pigeonhole
  ]
  scope := "Every line-based resolution refutation of the non-onto pigeonhole formula \
    PHP^(n+1)_n has at least 2^⌊n/24⌋ lines, by the Beame–Pitassi bottleneck argument. Proof \
    size is not solver runtime."

register_result "communication" where
  title := "Communication: disjointness resists randomness"
  topic := "communication complexity"
  sources := [
    { paper := KalyanasundaramSchnitger1992, theorem := unverified, locator := unverified },
    { paper := Razborov1992, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Communication.PublicCoin.le_mul_ecomplexityFun_disjointness_add
  ]
  scope := "n ≤ 2^16·R + 2^12 in ℕ∞, where R is the public-coin complexity of disjointness on \
    n-bit strings with error 1/3: the least, over distributions on binary protocol trees with \
    error at most 1/3 on every input pair, of the largest tree depth in the support (depth \
    counts unreachable branches). Stated for this infimum rather than per protocol."

register_result "communication-tiling-fooling" where
  title := "Fooling sets bound arbitrary monochromatic tilings"
  topic := "communication complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Lemma 12.8",
      locator := "Web draft 2007-01-08; printed p. 224 / PDF p. 240" }
  ]
  theorems := [Cslib.Communication.IsFoolingSet.card_le_partition,
    Cslib.Communication.IsFoolingSet.card_le_tilingNumber]
  scope := "A finite fooling set for one label injects into pieces with that label in every \
    arbitrary finite labelled rectangle partition. Its cardinality bounds the minimum \
    tilingNumber in extended naturals; no protocol-tree realization is assumed."

register_result "communication-tiling-rank" where
  title := "Zero/one matrix rank bounds arbitrary monochromatic tilings"
  topic := "communication complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 12.10",
      locator := "Web draft 2007-01-08; printed p. 224 / PDF p. 240" }
  ]
  theorems := [Cslib.Communication.RectanglePartition.rank_communicationMatrix_le,
    Cslib.Communication.rank_communicationMatrix_le_tilingNumber]
  scope := "The zero/one communication matrix over a commutative semiring with the strong \
    rank condition has rank at most the true-labelled pieces of every arbitrary tiling, \
    hence at most the minimum tiling number. Finite columns; fields are included. \
    This is not a sign-matrix rank bound or a protocol-realization theorem."

register_result "communication-rank-distinct-rows" where
  title := "Zero/one rank bounds deterministic communication from above"
  topic := "communication complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 12, Exercises 4 (corrected) and 6",
      locator := "Web draft 2007-01-08; printed p. 232 / PDF p. 248" }
  ]
  theorems := [Cslib.Communication.card_image_le_two_pow_rank,
    Cslib.Communication.ecomplexityFun_le_rank_add_one,
    Cslib.Communication.le_rank_of_injective,
    Cslib.Communication.clog_le_ecomplexityFun_of_injective]
  scope := "A zero/one matrix of rank r over a field has at most 2^r distinct rows. Hence \
    C(f) <= rank_K M(f) + 1 for finite inputs and every field K; the printed Exercise 4 lacks \
    its relation symbol, and this is its evident repair. Pairwise distinct rows on n-bit \
    inputs give rank >= n and C(f) >= ceil(log2 n), with no n >= 1 hypothesis. C(f) is \
    the depth of leaf-labelled protocol trees in which both players know the output."

-- Outside-fleet source check: SamuelSchlesinger (codex-coord-20261111-1634),
-- https://github.com/cslib-community/cslib-frontier/pull/6262#pullrequestreview-5947135257
register_result "communication-clique-independent-set" where
  title := "Clique versus independent set in O(log² n) bits"
  topic := "communication complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 12, Exercise 8",
      locator := "Web draft 2007-01-08; printed p. 232 / PDF p. 248" }
  ]
  theorems := [Cslib.Communication.ecomplexity_clique_indepSet_le]
  scope := "For every simple graph on a finite vertex type with n vertices, deterministic \
    protocol trees in which Alice holds a clique C and Bob an independent set I and both \
    learn |C ∩ I| (a natural number, at most one) need depth at most 3 (floor(log2 n) + 1)^2, \
    uniformly in the graph. The open second question of the exercise is not addressed."
-- https://github.com/cslib-community/cslib-frontier/pull/6259#pullrequestreview-5947134959
register_result "communication-aho-ullman-yannakakis" where
  title := "Monochromatic tilings give O(log² χ) deterministic protocols"
  topic := "communication complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 12, Exercise 7",
      locator := "Web draft 2007-01-08; printed p. 232 / PDF p. 248" }
  ]
  theorems := [Cslib.Communication.RectanglePartition.ecomplexityFun_run_le,
    Cslib.Communication.ecomplexityFun_le_eight_mul_log_tilingNumber_sq]
  scope := "A labelled rectangle partition with t pieces gives a deterministic protocol \
    tree of depth at most 2 ceil(log2 t) ceil(log2 (t+1)); hence C(f) <= 8 floor(log2 chi(f))^2 \
    for finite input types and any nonempty output type (the draft: Boolean f on n-bit \
    strings). chi is the minimum tiling number; the cover form O(N0 N1) is not claimed."

register_result "communication-tiling-discrepancy" where
  title := "Discrepancy bounds the minimum arbitrary monochromatic tiling size"
  topic := "communication complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Lemma 12.11",
      locator := "Web draft 2007-01-08; printed p. 225 / PDF p. 241" }
  ]
  theorems := [Cslib.Communication.one_le_tilingNumber_mul_discrepancy,
    Cslib.Communication.one_div_discrepancy_le_tilingNumber]
  scope := "Any PMF on finite rectangular input sets: one is at most minimum tiling size \
    times discrepancy, and reciprocal discrepancy is at most that finite minimum. \
    Uniform equal bit cubes recover the draft normalization. A PMF excludes empty input \
    products; the tiling model separately permits empty products and charged empty pieces."

register_result "communication-inner-product" where
  title := "Communication: inner product resists randomness"
  topic := "communication complexity"
  sources := [
    { paper := ChorGoldreich1988, theorem := unverified, locator := unverified },
    { paper := KushilevitzNisan1997, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Communication.PublicCoin.le_two_mul_ecomplexityFun_dotProduct_add_three
  ]
  scope := "n ≤ 2·R + 3 in ℕ∞, where R is the public-coin complexity with error 1/3 of the \
    inner product modulo two of n-bit strings (least worst-case tree depth over distributions \
    on protocol trees with per-input error at most 1/3), via the discrepancy method. Stated \
    for this infimum rather than per protocol."

register_result "communication-spectral-discrepancy" where
  title := "Uniform discrepancy bounded by the Euclidean operator norm"
  topic := "communication complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Lemma 12.13 (corrected operator-norm version)",
      locator := "Web draft 2007-01-08; printed p. 225 / PDF p. 241" }
  ]
  theorems := [Cslib.Communication.discrepancy_uniformOfFintype_le_l2_opNorm,
    Cslib.Communication.discrepancy_uniformOfFintype_mul_sqrt_card_le_l2_opNorm,
    Cslib.Communication.discrepancy_bitString_le_l2_opNorm]
  scope := "Finite nonempty rectangular input sets and uniform PMF: discrepancy is at most \
    the real sign matrix's Euclidean operator norm divided by sqrt(|X|*|Y|), or by 2^n \
    on equal n-bit cubes. Decidable equality on columns. The sign convention differs by \
    an overall minus sign from the draft. This corrects its false unrestricted eigenvalue \
    bound; no general spectral-radius or numerical norm-computation claim is made."

register_result "sipser-lautemann" where
  title := "Sipser–Gács–Lautemann: BPP lies in the second polynomial level"
  topic := "randomized complexity"
  sources := [
    { paper := Sipser1983, theorem := unverified, locator := unverified },
    { paper := Lautemann1983, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.BPP_subset_SigmaP_two_inter_PiP_two
  ]
  scope := "BPP ⊆ Σ₂ ∩ Π₂ for arbitrary injective encodings: BPP uses a total native \
    polynomial-time test on fair random strings, correct with probability at least 2/3 on every \
    input; Σ₂ and Π₂ use total native polynomial-time tests with explicit polynomial \
    quantifier blocks. No derandomization assumption."

register_result "seedless-extraction-impossibility" where
  title := "Deterministic seedless extraction fails even with only one bit of entropy loss"
  topic := "randomized complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 16, exercise 7",
      locator := "January 8, 2007 draft, printed page 319 (PDF page 335)" }
  ]
  theorems := [
    Cslib.Probability.exists_minEntropy_map_first_eq_pure,
    Cslib.Probability.not_isExtractor_bitString
  ]
  scope := "For positive n and m, every deterministic map from n bits to m bits has a finite \
    source of real min-entropy at least n - 1 whose first output bit is constant and whose \
    output distance from uniform is at least 1/2. No efficiency hypothesis. Exercise 12 and \
    the broader extractor objectives are not covered."

register_result "chor-goldreich" where
  title := "Chor–Goldreich: the inner product extracts from two weak sources"
  topic := "randomized complexity"
  sources := [
    { paper := ChorGoldreich1988, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Probability.isTwoSourceExtractor_dotProduct,
    Cslib.Probability.sum_mul_abs_bias_dotProduct_le,
    Cslib.Probability.exists_minEntropy_bind_dotProduct_eq_pure
  ]
  scope := "Bit strings indexed by a finite type of size n and arbitrary independent sources \
    with real min-entropy bounds k₁ and k₂: the inner product modulo two is within statistical \
    distance 2^((n - k₁ - k₂)/2)/2 of a uniform bit; the strong form bounds the average bias \
    over the second source by 2^((n - k₁ - k₂)/2); orthogonal uniform sources show the bound \
    fails at k₁ + k₂ = n. Information-theoretic; no running time asserted."

register_result "schoening" where
  title := "Schöning: 3-SAT in time (4/3)^n on the randomized word RAM"
  topic := "SAT algorithms"
  sources := [
    { paper := Schoening1999, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Algorithms.WordRAM.Schoening.ampProgram_spec,
    Cslib.Algorithms.WordRAM.Schoening.ampProgram_failure_eq,
    Cslib.Algorithms.WordRAM.Schoening.ampProgram_failure_le_exp,
    Cslib.Algorithms.WordRAM.Schoening.ampTime_le
  ]
  scope := "One fixed program of the library's unit-cost randomized word RAM over the standard \
    basis (truncated subtraction, x / 0 = 0, x % 0 = x; unit-cost rand), for every clause width \
    k ≥ 3 and words of O(log(n + k + L + c)) bits on input k :: c :: encode φ of length L: up \
    to R = ⌈(3n + 1)(2(k - 1)/k)^n (k/(k - 1))^(k - 3)⌉·c trials, every path halting within \
    900(n + k + L + 1)³(2 - 2/k)^n(c + 1) steps, no false positives, failure probability \
    exactly (1 - p)^R and at most e^(-c) on satisfiable k-CNFs. k = 3 gives (4/3)^n; not PPSZ."

register_result "subexponential-sat" where
  title := "OpenAI: the Exponential Time Hypothesis is false"
  topic := "fine-grained complexity"
  sources := [
    { paper := OpenAI2026ETH, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.CountingNativeEndpoint.decidableInSubexpTime_KSAT,
    Cslib.Complexity.CountingNativeEndpoint.satExponent_eq_zero,
    Cslib.Complexity.CountingNativeEndpoint.not_ETH,
    Cslib.Complexity.CountingNativeEndpoint.not_SETH
  ]
  scope := "For every fixed clause width k, k-SAT under the explicit binary encoding encCNF is \
    decidable by native machines in time 2^(δn)·poly(L) for every δ > 0, where n counts the \
    occurring variables and L is the encoded length; every fixed-width SAT exponent is zero; \
    the library's ETH and SETH are false. Interpolation-scale bound only, not the manuscript's \
    sharper headline runtime."

register_result "subexponential-sat-count" where
  title := "OpenAI: exact subexponential model counting for bounded-width CNF"
  topic := "SAT algorithms"
  sources := [
    { paper := OpenAI2026ETH, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.CountingNativeEndpoint.exists_modelCounter
  ]
  scope := "For each width k, one deterministic native machine computes the exact model count \
    of every CNF over ℕ whose clauses have at most k literals, in time \
    O(⌈2^(A·s(n))⌉·(L + 1)^e) and space O((L + 1)^b) for constants A, e, b, where n is the \
    number of variables, L the length of encCNF φ and s(n) = n(log log(n + 16))²/√log(n + 16) \
    the interpolation scale. Not the manuscript's sharper headline runtime."

register_result "partial-mcsp" where
  title := "Ilango: Partial MCSP is hard under the Exponential Time Hypothesis"
  topic := "meta-complexity"
  sources := [
    { paper := Ilango2020FOCS, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP,
    Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP_tableSize,
    Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP_encBinary,
    Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP_binaryGate,
    Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP_binaryGate_encBinary
  ]
  scope := "Under the library's ETH, PartialMCSP on m-variable partial truth tables is not \
    decidable by deterministic multi-tape machines in time 2^o(m log m) = N^o(log log N), \
    N = 2^m, with explicit unary or binary size-threshold encodings and De Morgan all-gate or \
    binary-gate cost. Conditional: the library also refutes ETH (subexponential-sat), so the \
    premise is false; the implications remain valid."

register_result "partial-mcsp-rp-hard" where
  title := "Hirahara: Partial MCSP is NP-hard under randomized reductions"
  topic := "meta-complexity"
  sources := [
    { paper := Hirahara2022, theorem := "Theorem I.2",
      locator := "p. 971, \"In particular\"" }
  ]
  theorems := [
    Cslib.PartialMCSP.rpHard,
    Cslib.PartialMCSP.rpHard_encBinary,
    Cslib.PartialMCSP.rpReducible_GapCMMSA_PartialMCSP,
    Cslib.PartialMCSP.NP_subset_BPP_of_mem_BPP,
    Cslib.PartialMCSP.NP_subset_coRP_of_mem_coRP
  ]
  scope := "Every NP language reduces to PartialMCSP (the partial truth table, then the size \
    threshold in unary, or in binary for rpHard_encBinary) by a polynomial-time randomized \
    many-one reduction with one-sided error: yes maps to yes always, no to no with probability \
    at least 2/3. Library route: from the library's GapCMMSA Δ g 1 (NP-hard via label cover) by \
    the library's own seeded construction and analysis; the source fixes the statement, not the \
    proof. The inapproximability and average-case forms of Theorem I.2 are not formalized. \
    The BPP and coRP inclusions are conditional on PartialMCSP being in BPP or coRP; they follow \
    from the reduction and are not stated separately in the source."

register_result "multi-mcsp-np-hard" where
  title := "Ilango–Loff–Oliveira: Multi-output MCSP is NP-hard under randomized reductions"
  topic := "meta-complexity"
  sources := [
    { paper := IlangoLoffOliveira2020, theorem := "Theorem 4",
      locator := "p. 22:5; reduction in Section 4.2, pp. 22:20–22:21" }
  ]
  theorems := [
    Cslib.MultiMCSP.rpHard,
    Cslib.MultiMCSP.rpHard_pos,
    Cslib.MultiMCSP.rpReducible_gapSetCover,
    Cslib.MultiMCSP.NP_subset_BPP_of_mem_BPP,
    Cslib.MultiMCSP.NP_subset_coRP_of_mem_coRP
  ]
  scope := "Every NP language reduces to Multi-output MCSP (n, m and s in unary, then the m \
    tables) by a polynomial-time randomized many-one reduction with one-sided error: yes maps \
    to yes always, no to no with probability at least 2/3; the reduction lands in Definition \
    1's positive instances. Over any De Morgan basis: Boolean.DeMorgan.interpretation is \
    Definition 1's constant-free AND/OR/NOT basis, Boolean.interpretation the library variant \
    with constants. Library route: from the library's GapSetCover 3 rather than Trevisan's \
    bounded Set Cover; soundness by a union bound over small circuits in place of Lemma 16; \
    windows as OR chains rather than canonical DNFs; the positions of the ground list in \
    place of its distinct elements. The BPP and coRP inclusions are conditional on Multi-MCSP \
    being in BPP or coRP; they follow from the reduction and are not stated separately in the \
    source."

register_result "magnification" where
  title := "McKay–Murray–Williams: barely superlinear circuit lower bounds for MCSP separate P \
    from NP"
  topic := "meta-complexity"
  sources := [
    { paper := McKayMurrayWilliams2019, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.MCSP.not_NP_subset_PPoly_of_yesSet_pow_hard,
    Cslib.MCSP.P_ne_NP_of_yesSet_pow_hard,
    Cslib.MCSP.exists_complexity_yesSet_le_of_NP_subset_PPoly,
    Cslib.MCSP.exists_complexity_yesSet_pow_le_of_NP_subset_PPoly
  ]
  scope := "If NP ⊆ P/poly (bit-string languages, native multi-tape NP), decision MCSP[s] on \
    2^n-bit truth tables in standard binary order has De Morgan circuits of size \
    2^n·c·(n + s(n) + 1)^c, counting all operation gates. Hence if for some k and every c > 0 \
    some 2^n-bit slice of MCSP[n^k] needs more than 2^n·c·(n + 1)^c gates, then NP ⊄ P/poly \
    and P ≠ NP. Size-only lower-bound hypothesis."

register_result "gap-mcsp-magnification" where
  title := "Oliveira–Pich–Santhanam: N^(1+ε) lower bounds for Gap-MCSP imply NP ⊄ P/poly"
  topic := "meta-complexity"
  sources := [
    { paper := OliveiraPichSanthanam2019, theorem := "Theorem 1.4 (ECCC TR18-158 Theorem 4)",
      locator := unverified }
  ]
  theorems := [
    Cslib.MCSP.not_NP_subset_PPoly_of_gapMCSP_hard,
    Cslib.MCSP.P_ne_NP_of_gapMCSP_hard,
    Cslib.MCSP.exists_gapMCSP_separator_of_NP_subset_PPoly
  ]
  scope := "If for some ε > 0 and every small enough β > 0 (eventually as β → 0⁺), for \
    infinitely many n no Boolean function on 2^n-bit truth tables that accepts every \
    yes-instance and rejects every no-instance of Gap-MCSP[⌊2^(βn)/(10n)⌋₊, ⌊2^(βn)⌋₊] has \
    De Morgan complexity at most N^(1+ε) (N = 2^n, all operation gates counted), then \
    NP ⊄ P/poly and P ≠ NP. The source's constant c = 10. Proof route: the \
    McKay–Murray–Williams circuits for MCSP[s] under NP ⊆ P/poly separate Gap-MCSP[s₁, s₂] \
    whenever s₁ ≤ s₂; OPS's own proof through the efficient anti-checker (Lemma 4.1, registered \
    as efficient-anti-checker) is not formalized."

register_result "matrix-multiplication" where
  title := "Matrix multiplication: the exponent is at most 9/4"
  topic := "algebraic complexity"
  sources := [
    { paper := Pass2026, theorem := unverified, locator := unverified },
    { paper := OpenAI2026MatrixMultiplication, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.MatrixMultiplication.admissibleExponent_nine_quarters,
    Cslib.Circuits.Arithmetic.MatrixMultiplication.omega_le_nine_quarters
  ]
  scope := "Over every field of characteristic zero, every τ > 9/4 is an admissible exponent: \
    for every ε > 0, exact n × n matrix multiplication has nonuniform arithmetic circuits of \
    at most c·n^(τ + ε) gates, addition, multiplication and constant gates each charged one, \
    inputs and outputs free; hence ω ≤ 9/4. No uniform generation, explicit constants or \
    integer bit complexity."

register_result "depth-five-imm" where
  title := "OpenAI: homogeneous depth-five circuits for iterated matrix multiplication"
  topic := "algebraic complexity"
  sources := [
    { paper := OpenAI2026DepthFive,
      theorem := "Corollary 6.1 (characteristic zero); Theorem 1.1 is its complex case",
      locator := "§6, p. 19; §1.1, p. 2" }
  ]
  theorems := [
    Cslib.Circuits.DepthFive.exists_forall_rpow_le_size,
    Cslib.Circuits.DepthFive.rpow_le_size
  ]
  scope := "Over every field of characteristic zero and for every n ≥ exp 29200, every \
    syntactically homogeneous ΣΠΣΠΣ circuit computing IMM_{n,n} as a formal polynomial has at \
    least n^(√n/400) lower product, middle sum and upper product gates; bottom linear forms \
    are unrestricted and gates are shared. The count is of the normalized model \
    Cslib.Circuits.DepthFive.Circuit, which is at most the source's gate count; no formal \
    conversion from a layered circuit is proved. The source's threshold is unspecified; here \
    it is exp 29200, not optimized. Lower bound only; the matching construction is the \
    entry depth-five-imm-upper. Not proved in positive characteristic."

register_result "depth-five-imm-upper" where
  title := "OpenAI: a homogeneous depth-five circuit for iterated matrix multiplication"
  topic := "algebraic complexity"
  sources := [
    { paper := OpenAI2026DepthFive, theorem := "the block construction of §6",
      locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.DepthFive.exists_circuit_size_le_rpow,
    Cslib.Circuits.DepthFive.exists_circuit_imm_of_le_mul
  ]
  scope := "Over every commutative semiring and for every n ≥ 2, some syntactically \
    homogeneous ΣΠΣΠΣ circuit computes IMM_{n,n} as a formal polynomial with at most \
    n^(√n + 4) lower product, middle sum and upper product gates; for n ≤ r·t the exact count \
    is r·n^(t+1) + r·n² + n^(r+1). Normalized model Cslib.Circuits.DepthFive.Circuit: leaves \
    and bottom sums are not counted, and there are n^(r+1) upper products where the source \
    has n^(r-1). With depth-five-imm the size is n^Θ(√n) over characteristic zero."

register_result "hitting-set-derivative-closed" where
  title := "Polynomial hitting sets for small partial-derivative spaces"
  topic := "algebraic complexity"
  sources := [
    { paper := BhardwajEtAl2026, theorem := "Theorems 1.1 and 4.1 (revision 1)",
      locator := "§1, §4" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.isHittingSet_logHittingSet,
    Cslib.Circuits.Arithmetic.aeval_logCurve_ne_zero,
    Cslib.Circuits.Arithmetic.isHittingSet_sum_pow
  ]
  scope := "Over a field of characteristic zero, a nonzero n-variate polynomial lying in a \
    space of dimension at most r closed under all partial derivatives does not vanish on the \
    curve ln(1 + (i+1)t) truncated below degree n·r² + r; the points of the curve at \
    t = 0, …, d(n·r² + r) are a hitting set for such polynomials of degree at most d, and \
    sums of s d-th powers of linear forms have a hitting set of d(n·(s(d+1))² + s(d+1)) + 1 \
    points. Existence and size of an explicit set only: no bit complexity, no black-box \
    algorithm model, nothing in positive characteristic, and not the source's extension to \
    noncommutative ABPs."

register_result "support-concentrating-shifts" where
  title := "Support-concentrating shifts for multilinear polynomials of small split rank"
  topic := "algebraic complexity"
  sources := [
    { paper := ForbesSaptharishiShpilka2014,
      theorem := "Theorem 4.1 with Lemma 4.4, for individual degree one",
      locator := "§4, pp. 21–23 (arXiv v1)" },
    { paper := Shpilka2026, theorem := "Theorem 2.3 and Corollary 2.4, for δ = 1",
      locator := "§2, p. 5" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.exists_mem_concentratingShifts_perfectHashFamily,
    Cslib.Circuits.Arithmetic.card_concentratingShifts_perfectHashFamily_le,
    Cslib.Circuits.Arithmetic.exists_mem_concentratingShifts
  ]
  scope := "Over a field of characteristic zero, an explicit set of at most \
    (n²·2^(25(⌊lg w⌋+1)) + 1)(n·2^(⌊lg w⌋+1) + 1) points such that every nonzero multilinear \
    polynomial in n variables that is a sum of w products across every split of ⌊lg w⌋ + 1 \
    variables from the rest has, after shifting by one of the points, a monomial with at most \
    ⌊lg w⌋ variables. Individual degree one only, by a direct argument and not the sources' \
    rank condensers; the support bound ⌊lg w⌋ is smaller than the sources' ⌊lg w²⌋. The set is \
    built from a perfect hash family of the library and not from the Klivans–Spielman \
    generator. Split rank is a decomposition into products, not a coefficient-matrix rank or \
    a branching program. No hitting set for read-once branching programs is claimed here."

register_result "hitting-set-multilinear-any-order-roabp" where
  title := "Polynomial-size hitting sets for multilinear any-order ROABPs"
  topic := "algebraic complexity"
  sources := [
    { paper := Shpilka2026, theorem := "Theorem 1.1, in characteristic zero; Lemmas 3.1–3.4",
      locator := "§1.1 p. 3, §3 pp. 6–9" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.isHittingSet_anyOrderHittingSet_roabp,
    Cslib.Circuits.Arithmetic.isHittingSet_anyOrderHittingSet,
    Cslib.Circuits.Arithmetic.card_anyOrderHittingSet_le,
    Cslib.Circuits.Arithmetic.IsAnyOrderROABP.splitRankLE
  ]
  scope := "Over a field of characteristic zero, an explicit set of points in Fⁿ, of size \
    bounded by an explicit polynomial in n and w, that contains a non-root of every nonzero \
    multilinear n-variate polynomial computed by width-w read-once oblivious branching \
    programs in every variable order; more generally of every multilinear polynomial that is \
    a sum of w products across every split of the variables. Characteristic zero only: the \
    source's positive-characteristic case rests on an unpublished hitting set. The perfect \
    hash family and the shifts are the library's own constructions, so the size bound \
    differs from the source's. Existence and size of an explicit set only: no bit \
    complexity and no black-box algorithm model. The converse of Nisan's characterisation \
    is not proved."

register_result "hitting-set-set-multilinear-depth-three" where
  title := "Hitting sets for set-multilinear depth-3 circuits with small variable sets"
  topic := "algebraic complexity"
  sources := [
    { paper := Shpilka2026, theorem := "Theorem 1.2, in characteristic zero; Lemma 3.4",
      locator := "§1.1 p. 3, §3 pp. 8–9" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.isHittingSet_setMultilinearHittingSet_sum_prod,
    Cslib.Circuits.Arithmetic.isHittingSet_setMultilinearHittingSet,
    Cslib.Circuits.Arithmetic.card_setMultilinearHittingSet_le
  ]
  scope := "Over a field of characteristic zero, for variables in n blocks of d, an explicit \
    set of points of size at most an explicit polynomial in n, d and s times \
    (d + 1)^(⌊lg s⌋ + 1), that contains a non-root of every nonzero sum of s products of n \
    linear forms, the j-th in the variables of block j; more generally of every polynomial \
    whose monomials have at most one variable of each block, to the first power, and that is \
    a sum of s products across every union of blocks. Characteristic zero only: the source's \
    positive-characteristic case rests on an unpublished hitting set. Blocks are Fin n × Fin d, \
    not a general partition. The support-concentrating shifts for individual degree d have \
    the statement the source cites from Forbes–Saptharishi–Shpilka, with a proof that is not \
    from a source; the perfect hash family is the library's, so the size bound differs from \
    the source's. Existence and size of an explicit set only: no bit complexity and no \
    black-box algorithm model."

register_result "hitting-set-constant-depth" where
  title := "Subexponential hitting sets for constant-depth formulas from the LST lower bound"
  topic := "algebraic complexity"
  sources := [
    { paper := LimayeSrinivasanTavenas2021, theorem := "Corollary 6, via Lemma 18",
      locator := "printed p. 5 and §6 p. 13, ECCC TR21-081 rev. 1" },
    { paper := ChouKumarSolomon2019, theorem := "Theorem 2.3",
      locator := "printed p. 3 (arXiv:1803.05933v1)" },
    { paper := BhattacharjeeEtAl2025, theorem := "Theorems 4.1 and 6.1",
      locator := "printed pp. 19–20 and 28 (arXiv:2506.23214v1)" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.eventually_isHittingSet_constantDepthHittingSet_rpow,
    Cslib.Circuits.Arithmetic.eventually_isHittingSet_constantDepthHittingSet_circuit_rpow,
    Cslib.Circuits.Arithmetic.eventually_isHittingSet_constantDepthHittingSet,
    Cslib.Circuits.Arithmetic.eventually_card_constantDepthHittingSet_le,
    Cslib.Circuits.Arithmetic.eventually_isHittingSet_constantDepthHittingSet_circuit
  ]
  scope := "Over a field of characteristic zero, for every product-depth Δ, exponent c and \
    real ε > 0, for all large n: an explicit set of at most 2^(n^ε) points of Kⁿ containing a \
    non-root of every nonzero polynomial computed by an unbounded fan-in formula of \
    product-depth at most Δ with at most n^c nodes, and, at a larger exponent, by a simple \
    circuit of product-depth at most Δ with at most n^c gates. A finite form of LST \
    Corollary 6, which is an identity test with running time (s^(Δ+1) n)^O(n^μ) for depth \
    o(log log log n): here constant product-depth, existence and size of an explicit set with \
    non-explicit large-n thresholds, no running time or uniformity, characteristic zero only."

register_result "hitting-set-noncommutative-abp" where
  title := "Quasipolynomial hitting sets of matrices for non-commutative ABPs"
  topic := "algebraic complexity"
  sources := [
    { paper := ForbesShpilka2013,
      theorem := "Construction 4.1, Lemmas 4.2, 4.3, 4.5 and Theorem 4.6, for homogeneous \
        layered programs; not Corollary 4.7",
      locator := "§1.1 pp. 2–3, §4 pp. 22–24 (arXiv:1209.2408v2)" },
    { paper := AgrawalGurjarKorwarSaxena2015,
      theorem := "Theorem 1, in the adapted form of hitting-set-roabp-unknown-order",
      locator := "§1 and §3 of arXiv:1406.7535" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.exists_mem_noncommABPHittingSet_lift_ne_zero,
    Cslib.Circuits.Arithmetic.card_noncommABPHittingSet_le
  ]
  scope := "Over a field of characteristic zero, an explicit set of n-tuples of \
    (d + 1) × (d + 1) matrices such that every nonzero polynomial computed by a homogeneous \
    layered non-commutative branching program of degree d in n variables with all layers of \
    width at most W is nonzero at one of the tuples. The set is the image of the hitting set \
    for read-once oblivious programs in d variables, width W and layer degree n - 1, so its \
    size is (ndW)^O(log d). The reduction to read-once oblivious programs is that of \
    Forbes–Shpilka; the hitting set for those is the library's adaptation of \
    Agrawal–Gurjar–Korwar–Saxena (a different weight family, levels combined one at a \
    time), not Forbes–Shpilka's generator, so the size is neither paper's bound. Homogeneous \
    layered programs only. No white-box algorithm and no bit complexity."

register_result "hitting-set-roabp-unknown-order" where
  title := "Quasipolynomial hitting sets for ROABPs in an unknown order"
  topic := "algebraic complexity"
  sources := [
    { paper := AgrawalGurjarKorwarSaxena2015,
      theorem := "Theorem 1, for univariate layers, in characteristic zero; Lemmas 6 and 8",
      locator := "§1 and §3 of arXiv:1406.7535" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.isHittingSet_roabpHittingSet,
    Cslib.Circuits.Arithmetic.card_roabpHittingSet_le,
    Cslib.Circuits.Arithmetic.roabpPrime_le
  ]
  scope := "Over a field of characteristic zero, an explicit set of points of Fⁿ that contains \
    a non-root of every nonzero n-variate polynomial computed by a width-w read-once \
    oblivious branching program in some order of the variables with layer entries of degree \
    at most δ; the set does not depend on the order. Its size is at most \
    (⌈lg n⌉ + 1) p^⌈lg n⌉ (nδ(nδp + 1 + p)^⌈lg n⌉ + 1) for a prime p ≤ 2(2n²w⁸ + δ + 1), \
    which is (nδw)^O(log n). Univariate layers only, not the source's sparse-factor layers. \
    The weights are aⁱ⁺¹ mod p for one prime p instead of the source's (δ + 1)ⁱ mod q over \
    many primes, and the levels are combined one at a time, so the bound is not the \
    source's. Characteristic zero only. Existence and size of an explicit set: no bit \
    complexity and no black-box algorithm model."

register_result "hitting-set-sparse" where
  title := "Ben-Or–Tiwari: a hitting set for sparse polynomials"
  topic := "algebraic complexity"
  sources := [
    { paper := BenOrTiwari1988, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.isHittingSet_primePowers,
    Cslib.Circuits.Arithmetic.isHittingSet_powerHittingSet
  ]
  scope := "Over a domain of characteristic zero, the s points (p₁ʲ, …, pₙʲ), j < s, of powers \
    of the first n primes hit every nonzero n-variate polynomial with at most s monomials, \
    whatever its degree; more generally for any point whose monomials are pairwise distinct. \
    Zero test only: no interpolation algorithm, no bit complexity, nothing in positive \
    characteristic."

register_result "hitting-set-sparse-affine-orbit" where
  title := "Polynomial-size hitting sets for affine orbits of sparse polynomials"
  topic := "algebraic complexity"
  sources := [
    { paper := BhargavaSengupta2026,
      theorem := "Theorem 1.2 items 1 and 2, in characteristic zero; Lemmas 1.6, 3.1 and 3.2",
      locator := "§1.1 p. 3, §3 pp. 8–9, §4 pp. 9–10" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.isHittingSet_sparseOrbitHittingSet,
    Cslib.Circuits.Arithmetic.card_sparseOrbitHittingSet_le
  ]
  scope := "Over a field of characteristic zero, an explicit set of at most \
    (n² + 1)(2d(ns² + s) + 1) points of Fⁿ that contains a non-root of every nonzero \
    polynomial p(Ax + b) of degree at most d, with A an invertible matrix and p a polynomial \
    with at most s monomials. The key lemma: if all coordinates of u are nonzero, the partial \
    derivatives of the lowest nonzero homogeneous component of p(x + u) span a space of \
    dimension at most the number of monomials of p. Ordinary partial derivatives instead of \
    the source's Hasse derivatives, so characteristic zero throughout, although the source's \
    lemma holds in every characteristic. The curve is the library's ln(1 + (i + 1)t) \
    truncated below degree ns² + s, not the source's -ln(1 - it) truncated at that degree. \
    Not the degree-free hitting set over the reals, the lower bound, the applications to \
    other orbit classes, or the operation count. Existence and size of an explicit set only: \
    no bit complexity and no black-box algorithm model."

register_result "hitting-set-lower-bound" where
  title := "Heintz–Schnorr: hitting sets give lower bounds"
  topic := "algebraic complexity"
  sources := [
    { paper := HeintzSchnorr1980, theorem := unverified, locator := unverified },
    { paper := Agrawal2005, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.IsHittingSet.exists_notMem,
    Cslib.Circuits.Arithmetic.exists_ne_zero_forall_eval_eq_zero
  ]
  scope := "Over a field, if H is a hitting set for a class and T is a finite set of \
    monomials with more elements than H, some nonzero polynomial with monomials in T is not \
    in the class. Existence by a dimension count; the polynomial is not exhibited and its \
    complexity is not bounded."

/-! ## Further collected results -/

register_result "sharp-p-lowness" where
  title := "Exact characterization of #P oracle lowness"
  topic := "counting classes"
  sources := [
    { paper := KoeblerSchoeningTodaToran1992, theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.SharpPWithOracle_eq_SharpP_iff
  ]
  scope := "Equality of #P^A and #P on binary words iff A is in UP ∩ coUP. Uses strict \
    polynomial-time adaptive word-oracle verifiers, with resource bounds for \
    arbitrary replies; does not assert an oracle-machine counting characterization."

register_result "goldreich-sharp-three-sat-to-integer-permanent" where
  title := "#3SAT reduces to the permanent of small-integer matrices"
  topic := "counting classes"
  sources := [
    { paper := Goldreich2007Draft, theorem := "Proposition 6.21",
      locator := "February 2007 draft r3.pdf, PDF pp. 24–27; printed pp. 226–229" }
  ]
  theorems := [
    Cslib.Complexity.goldreich_prop_6_21,
    Cslib.Complexity.metricReducible_sharpThreeSAT_intPermanent
  ]
  scope := "c = 12 and I = {-1, 0, 1, 2, 3}: a native polynomial-time map from encCNF to the \
    dense integer-table encoding with perm(M_φ) = 12^m · #3SAT(φ) for every CNF φ with m \
    clauses, using Goldreich's Figure 6.3 gadget. Counts are over the variables occurring in \
    φ; formulas with an empty or over-long clause map to the 1×1 zero matrix. Not the 0/1 \
    permanent endpoint (Proposition 6.22) nor Theorem 6.20."


register_result "goldreich-nonnegative-permanent-reduction" where
  title := "Proposition 6.21 needs negative entries unless P = NP"
  topic := "counting complexity"
  sources := [
    { paper := Goldreich2007Draft, theorem := "Exercise 6.25",
      locator := "February 2007 draft r3.pdf, PDF p. 58; printed p. 260" }
  ]
  theorems := [Cslib.Complexity.exercise_6_25]
  scope := "Under P ≠ NP (any encoding): no non-zero integer c, set I of non-negative integers \
    (finite or not) and polynomial-time map from formulas (encCNF) to dense integer tables \
    (encIntTable) with entries in I and permanent c^m * #3SAT on every formula with clauses of \
    at most three literals. Negates more than the source requires (c need not be even or \
    positive). Outside-fleet source check: PR #6261, pullrequestreview-5947014802."

register_result "goldreich-approx-counting-np-hard-oracle" where
  title := "Approximate counting for a PC relation with an NP-hard S_R oracle"
  topic := "counting complexity"
  sources := [
    { paper := Goldreich2007Draft, theorem := "Exercise 6.39 (approximate-counting half)",
      locator := "February 2007 draft r3.pdf, PDF p. 62; printed p. 264" }
  ]
  theorems := [Cslib.Complexity.FNP.exists_approxCount_of_npHard]
  scope := "Every R in FNP (Goldreich's PC) whose language searchDomain R is NP-hard, hence \
    every PC-complete R; oracle enc '' searchDomain R; factor 1 ± 1/q(n), failure probability \
    2^(-n), natural-number output. The uniform-generation half is not covered. Outside-fleet \
    six-point source check: review 5953505829 on PR #6392."

register_result "gap-p-spp-lowness" where
  title := "GapP and SPP lowness characterize SPP"
  topic := "counting classes"
  sources := [
    { paper := FennerFortnowKurtz1994, theorem := unverified,
      locator := "Section 5" }
  ]
  theorems := [
    Cslib.Complexity.GapPWithOracle_eq_GapP_iff,
    Cslib.Complexity.SPPWithOracle_eq_SPP_iff
  ]
  scope := "Binary-word instances; strict adaptive oracle-verifier model. GapP is a \
    difference of two unsigned witness counts."

register_result "first-order-logspace" where
  title := "Fixed first-order queries are decidable in logarithmic space"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1999, theorem := "Theorem 3.1",
      locator := unverified }
  ]
  theorems := [
    Cslib.Logic.Vocabulary.queryLanguage_mem_L,
    Cslib.Logic.FO.Definable.queryLanguage_mem_L
  ]
  scope := "Fixed first-order sentences over finite relational vocabularies, with explicit \
    structure encoding and malformed-input rejection. Includes empty structures and \
    nullary relations; excludes constants and built-in order/BIT from the cited FO \
    convention."

register_result "nl-in-p" where
  title := "NL is contained in P"
  topic := "space complexity"
  sources := [
    { paper := Sipser2013, theorem := unverified,
      locator := "Section 8.5" },
    { paper := AroraBarak09, theorem := unverified,
      locator := "Section 4.1" }
  ]
  theorems := [
    Cslib.Complexity.NL_subset_P,
    Cslib.Complexity.mem_P_of_recognizesInSpace
  ]
  scope := "Finite-control native nondeterministic multi-tape machines and arbitrary \
    injective encodings. The stronger recognizer result permits nonterminating \
    branches with logarithmic workspace; deterministic polynomial-time \
    configuration reachability decides acceptance."

register_result "ladner-density" where
  title := "Ladner's density theorem for polynomial-time many-one reducibility"
  topic := "structural complexity"
  sources := [
    { paper := Ladner1975a, theorem := unverified, locator := unverified },
    { paper := Schoening1982, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.exists_isDecidable_notMem_P_lt,
    Cslib.Complexity.exists_mem_NP_notMem_P_lt,
    Cslib.Complexity.NPComplete.exists_NP_not_P_not_npComplete_lt,
    Cslib.Complexity.exists_isDecidable_between_of_notMem_P,
    Cslib.Complexity.exists_mem_NP_between_of_notMem_P
  ]
  scope := "Problems on binary words (encBits); total deterministic multi-tape polynomial-time \
    many-one reductions. Between any two problems A <ₘᵖ B on bit words with B decidable \
    (respectively A, B in NP) and B ∉ P, there is a decidable problem C (respectively in NP) \
    strictly between them; if P ≠ NP, every NP-complete language on bit words has an \
    NP-intermediate language strictly below it. Many-one (≤ₘᵖ) order and non-reductions only; \
    Ladner's polynomial-time Turing (≤ᵀᵖ) non-reduction and ≤ᵀᵖ-density forms are not included. \
    The hypothesis B ∉ P is required (∅ <ₘᵖ {[true]} has no intermediate)."

register_result "ppz-success" where
  title := "PPZ success probability for k-SAT"
  topic := "SAT algorithms"
  sources := [
    { paper := PPZ1997, theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.PPZ.round_success_of_satisfiable,
    Cslib.Complexity.PPZ.round_success
  ]
  scope := "CNF over Fin n, clauses of length at most k ≥ 1. One-round success probability \
    at least 2^(-(1 - 1/k)n); also a unique-solution theorem. Probabilistic \
    semantics only: these declarations do not certify native runtime."

register_result "schoening-success" where
  title := "Schöning randomized k-SAT success bound"
  topic := "SAT algorithms"
  sources := [
    { paper := Schoening1999, theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.Schoening.trial_success_of_length_le,
    Cslib.Complexity.Schoening.trial_success
  ]
  scope := "Satisfiable CNF over a finite variable type, width at most k ≥ 3, uniform start \
    and 3n local-search steps. Lower bound ((k-1)/k)^(k-3) · (k/(2(k-1)))^n / \
    (3n+1). Explicit factors are this formalization’s constants; no native runtime \
    assertion."

register_result "ov-sat-transfer" where
  title := "Williams split-and-list transfer from OV to SAT"
  topic := "fine-grained complexity"
  sources := [
    { paper := Williams2005, theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.DecidableInTimeO.decidableInExpTime_SAT
  ]
  scope := "An OV decider of time N^(2-ε) times a polynomial in dimension yields native SAT \
    time of exponent 1 - min(ε,1)/2 in occurring variables, with polynomial \
    encoded-input overhead. This records the transfer, not the separate conditional \
    OVH result or logarithmic-dimension OVH."

register_result "native-sparsification" where
  title := "Native algorithmic consequence of sparsification"
  topic := "fine-grained complexity"
  sources := [
    { paper := ImpagliazzoPaturiZane2001, theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.exists_decidableInExpTime_numVars_of_length
  ]
  scope := "For fixed width k and ε > 0, some natural c transfers a k-SAT decider of \
    clause-count exponent δ ≥ 0 to variable-count exponent ε + cδ. Native machines, \
    encCNF and polynomial encoded-length overhead; no new sharp sparsification \
    constant."

register_result "williams-square-root-space" where
  title := "Williams's square-root-space simulation of deterministic time"
  topic := "space complexity"
  sources := [
    { paper := Williams2025, theorem := "Theorem 1.1",
      locator := "arXiv:2502.17779v1, Section 3" }
  ]
  theorems := [
    Cslib.Complexity.DTIME_subset_DSPACE_sqrt
  ]
  scope := "For every time bound t(n) >= n and arbitrary injective input encoding, \
    DTIME(t) is contained in DSPACE(Nat.sqrt(t * (Nat.log2(t) + 1))). Finite binary \
    multitape machines, read-only input and visited-work-cell space; classes absorb \
    affine constants. No time-constructibility or monotonicity hypothesis."

register_result "blum-mansour-swap-regret" where
  title := "Blum–Mansour reduction from swap regret to external regret"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007, theorem := "Theorem 5 and Corollary 7", locator := "p. 1313" },
    { paper := Roughgarden2013CS364A, theorem := "Theorem 2.1",
      locator := "Lecture 18, Section 2, pp. 3–5" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.swap_regret_le_sum_regret,
    Cslib.MachineLearning.OnlineLearning.Experts.blumMansour_swap_regret_le,
    Cslib.MachineLearning.OnlineLearning.Experts.blumMansour_swap_regret_le_sqrt
  ]
  scope := "Experts setting with a finite set of n actions and arbitrary real loss sequences. \
    The reduction assumes the learner plays a stationary vector of the copies' distributions \
    and that copy j has regret at most R j on the losses scaled by the learner's probability of \
    j; it then bounds the swap regret against every swapping function by the sum of the R j. \
    With Hedge copies and losses in [-1, 1], swap regret is at most η T + n ln n / η, and \
    2 √(T n ln n) with the tuned rate when n ≥ 2 and T ≥ n ln n. Stationary vectors are \
    chosen classically; no running time is charged."

register_result "littlestone-vc-mistake-bound" where
  title := "VC dimension lower-bounds the optimal mistake bound"
  topic := "online learning"
  sources := [
    { paper := Littlestone1988, theorem := "Theorem 4", locator := "Section 3, p. 295" }
  ]
  theorems := [Cslib.MachineLearning.OnlineLearning.MistakeBound.evcDim_le_optimalMistakeBound]
  scope := "Every deterministic online learner for a Boolean class can be forced to make at least \
    the size of any finite shattered set in mistakes. Taking the supremum extends the paper's \
    finite-class comparison to arbitrary classes. For the empty class the two extended-natural \
    quantities are both zero, where Littlestone gives both quantities the value −1."

register_result "natarajan-cardinality-bound" where
  title := "Natarajan's cardinality bound for multiclass hypotheses"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Lemma 29.4", locator := "Section 29.2" }
  ]
  theorems := [Cslib.MachineLearning.PACLearning.ncard_le_card_pow_natarajanDim]
  scope := "For any class of functions from a finite domain X to a finite set of k labels, \
    its cardinality is at most |X|^d k^(2d), where d is its Natarajan dimension. Finiteness \
    of the domain gives a finite exponent, including for the empty class."

register_result "adaboost-training-error" where
  title := "AdaBoost training-error bound"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Theorem 10.2", locator := "pp. 135–137" },
    { paper := MohriRostamizadehTalwalkar2018, theorem := "Theorem 7.2", locator := "p. 149" }
  ]
  theorems := [
    Cslib.MachineLearning.Boosting.empiricalMiscount_adaBoost_le_prod,
    Cslib.MachineLearning.Boosting.empiricalMiscount_adaBoost_le_exp_sum,
    Cslib.MachineLearning.Boosting.empiricalMiscount_adaBoost_le_exp,
    Cslib.MachineLearning.Boosting.IsWeakLearner.empiricalMiscount_adaBoost_eq_zero
  ]
  scope := "AdaBoost on a finite labelled sample with a deterministic weak learner mapping \
    weights on the sample to a Boolean hypothesis. If every round has weighted error < 1, the \
    training error after T rounds is at most the product of 2 √(ε_t (1 - ε_t)), hence at most \
    exp(-2 Σ_t (1/2 - ε_t)²); if every \
    ε_t ≤ 1/2 - γ with γ ≥ 0, it is at most exp(-2 γ² T), and a weak learner of edge γ gives \
    a consistent output once log m < 2 γ² T. A round with ε_t = 0 stops AdaBoost with its \
    consistent hypothesis; vote ties predict false. Generalization is not covered."

register_result "fundamental-theorem-statistical-learning" where
  title := "The fundamental theorem of statistical learning on countable domains"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Theorem 6.7",
      locator := "Section 6.4, p. 72" }
  ]
  theorems := [
    Cslib.MachineLearning.PACLearning.tfae_hasFiniteVCDim,
    Cslib.MachineLearning.PACLearning.isPACLearnable_univ_iff_hasFiniteVCDim,
    Cslib.MachineLearning.PACLearning.isPACLearnable_realizableDistributions_iff_hasFiniteVCDim
  ]
  scope := "Binary classes with the 0-1 loss on a countable domain with measurable singletons. \
    Uniform convergence and learnability by every ERM use one sample-size threshold for all \
    ERMs, where the source lets it depend on the ERM rule; the equivalence is unaffected. \
    Agnostic learnability implies finite VC dimension on every domain with measurable \
    singletons (IsPACLearnable.hasFiniteVCDim_of_univ). The quantitative bounds of Theorem 6.8 \
    and the upper bounds on uncountable domains are not proved."

register_result "rlm-stability" where
  title := "Stability and oracle inequality of Tikhonov-regularized loss minimization"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Corollaries 13.6, 13.8 and 13.9",
      locator := "Sections 13.3.1 and 13.4" }
  ]
  theorems := [
    Cslib.MachineLearning.IsRLM.isReplaceOneStable_tikhonov,
    Cslib.MachineLearning.IsRLM.integral_trueRisk_le_tikhonov,
    Cslib.MachineLearning.IsRLM.integral_trueRisk_le_add_sqrt
  ]
  scope := "Regularizer r‖w‖² on a convex subset K of a real inner product space, losses convex \
    and ρ-Lipschitz on K, m i.i.d. examples from an arbitrary probability measure. The rule \
    minimizes over K and the comparator ranges over K. The replace-one stability rate proved is \
    ρ² / (r m), half the source's; the oracle inequalities are stated with the source's \
    constants. Integrability of the losses of the rule's output is a hypothesis."

register_result "rlm-smooth-stability" where
  title := "Stability and oracle inequality of Tikhonov-regularized loss minimization for smooth \
    losses"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Corollaries 13.7, 13.10 and 13.11",
      locator := "Sections 13.3.2 and 13.4" }
  ]
  theorems := [
    Cslib.MachineLearning.IsRLM.replaceOneGap_le_tikhonov_of_lipschitzWith_fderiv,
    Cslib.MachineLearning.IsRLM.integral_trueRisk_le_tikhonov_of_lipschitzWith_fderiv,
    Cslib.MachineLearning.IsRLM.integral_trueRisk_le_add_of_lipschitzWith_fderiv
  ]
  scope := "Regularizer r‖w‖² on a convex subset K of a real inner product space, losses convex \
    on K, nonnegative, and differentiable on the whole space with β-Lipschitz derivative, m \
    i.i.d. examples from an arbitrary probability measure. Corollaries 13.7 and 13.10 are proved \
    with the factor 5β / (r m) in place of the source's 48β / (r m); Corollary 13.11 keeps the \
    source's parameters, for which the factor 48 does not suffice. Integrability of the losses \
    of the rule's output is a hypothesis."

register_result "ridge-regression-learnability" where
  title := "Learnability by ridge regression"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Theorem 13.1", locator := "Section 13.1.1" }
  ]
  theorems := [
    Cslib.MachineLearning.IsRLM.integral_trueRisk_squaredLoss_le_add
  ]
  scope := "The squared loss (⟪w, x⟫ - y)² / 2 in a real inner product space, features of norm \
    at most 1 and labels in [-1, 1], the rule minimizing over the whole space, and comparators \
    of norm at most B, with the source's parameters m ≥ 150 B² / ε² and r = ε / (3 B²). \
    Integrability of the losses of the rule's output is a hypothesis."

register_result "srm-nonuniform-learnability" where
  title := "Countable unions of uniformly convergent classes are nonuniformly learnable by SRM"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Theorems 7.3 and 7.5",
      locator := "Theorem 7.3 in Section 7.1.1, p. 85; Theorem 7.5 in Section 7.2, pp. 87–88" }
  ]
  theorems := [
    Cslib.MachineLearning.PACLearning.isNonuniformLearnable_iUnion,
    Cslib.MachineLearning.PACLearning.isNonuniformLearnable_of_countable
  ]
  scope := "Domain and labels are arbitrary measurable spaces. Uniform convergence is an \
    explicit rate ε i m δ for m > 0 and δ > 0 with ε i m δ → 0; the learner for accuracy ε and \
    confidence δ is an SRM rule over pairs (i, h) and may depend on (ε, δ), following the \
    upstream IsPACLearnable conventions. Countable classes need measurable misclassification \
    sets. Theorem 7.5's explicit sample complexity is not stated, only learnability. The \
    converse characterization (Theorem 7.2) is not proved."

register_result "mdl-bound" where
  title := "Minimum description length bound for prefix-free descriptions"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Theorem 7.7",
      locator := "Section 7.3, p. 90" }
  ]
  theorems := [
    Cslib.MachineLearning.PACLearning.IsPrefixFreeDescription.mdl_bound,
    Cslib.MachineLearning.PACLearning.IsPrefixFreeDescription.measure_pi_exists_le_abs_sub_le
  ]
  scope := "Binary descriptions d : (α → β) → List Bool, prefix-free on the class, and \
    hypotheses with measurable misclassification sets, for m > 0 and δ > 0. With probability \
    at least 1 - δ every h satisfies L_D(h) ≤ L_S(h) + √((|d h| log 2 + log (2/δ)) / (2m)), \
    which is sharper than the source's |h| + ln (2/δ). Kraft's inequality is Mathlib's."

register_result "pac-bayes-mcallester" where
  title := "McAllester's PAC-Bayes bound and its Occam corollary"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Theorem 31.1 and Exercise 31.2",
      locator := "Section 31.1 and 31.3, pp. 416–418" },
    { paper := McAllester1999, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.PACBayes.measure_pi_exists_integral_risk_gt,
    Cslib.MachineLearning.PACBayes.measure_pi_exists_integral_risk_gt_log_div,
    Cslib.MachineLearning.PACBayes.measure_pi_exists_risk_gt
  ]
  scope := "Countable hypothesis index with measurable singletons, a prior fixed before the \
    sample, measurable losses in [0, 1], m ≥ 2 i.i.d. examples and δ > 0. With probability at \
    least 1 - δ every posterior Q with KL(Q ‖ P) < ∞, possibly depending on the sample, has \
    E_Q L_D ≤ E_Q L_S + √((KL(Q ‖ P) + log (m / δ)) / (2 (m - 1))); the proved form has \
    log (√m / δ). Point masses give the Occam bound with log (1 / P {i}). Measurable \
    hypothesis spaces, the kl form and Catoni's bound are not covered."

register_result "pac-bayes-kl" where
  title := "The PAC-Bayes-kl bound of Seeger and Maurer and its Occam form"
  topic := "statistical learning"
  sources := [
    { paper := Seeger2002, theorem := "Theorem 1 and Appendix A",
      locator := "Section 1.3, p. 239, and pp. 264–265" },
    { paper := Maurer2004, theorem := "Lemma 3", locator := "Section 2, p. 4" }
  ]
  theorems := [
    Cslib.MachineLearning.PACBayes.measure_pi_exists_binaryKL_integral_risk_gt,
    Cslib.MachineLearning.PACBayes.measure_pi_exists_binaryKL_risk_gt
  ]
  scope := "Countable hypothesis index with measurable singletons, a prior fixed before the \
    sample, measurable losses in [0, 1], m ≥ 1 i.i.d. examples and δ > 0. With probability at \
    least 1 - δ every posterior Q with KL(Q ‖ P) < ∞, possibly depending on the sample, has \
    kl(E_Q L_S ‖ E_Q L_D) ≤ (KL(Q ‖ P) + log ((m + 1) / δ)) / m, the binary relative entropy \
    in nats; Seeger states it for the 0-1 loss and Maurer's Lemma 3 extends it to [0, 1]. \
    Point masses give the Occam form with log (1 / P {i}). Maurer's log (2√m / δ) for m ≥ 8, \
    the square-root form through binary Pinsker, measurable hypothesis spaces and Catoni's \
    bound are not covered."

register_result "agnostic-vc-sharp-rate" where
  title := "Sharp agnostic sample complexity of classes of finite VC dimension"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Theorem 6.8",
      locator := "Section 6.4, pp. 72–73" }
  ]
  theorems := [
    Cslib.MachineLearning.PACLearning.measure_pi_not_isRepresentative_le_of_chainingSampleSize_le,
    Cslib.MachineLearning.PACLearning.isPACLearnerFor_univ_of_chainingSampleSize_le,
    Cslib.MachineLearning.PACLearning.sampleComplexity_univ_le_chainingSampleSize
  ]
  scope := "Upper bounds of items 1 and 2 only, on countable domains with measurable \
    singletons: uniform convergence and agnostic PAC learning by ERM from \
    (16384 d + 32 log (4/δ)) / ε² and (65536 d + 128 log (4/δ)) / ε² examples, where d bounds \
    the shattered sets. The constants are explicit and unoptimized. The lower bounds and the \
    realizable item 3 are not part of this entry, and uncountable domains need a measurability \
    hypothesis on the class."

register_result "gmw-zero-knowledge" where
  title := "Goldreich–Micali–Wigderson auxiliary-input zero-knowledge proofs for NP"
  topic := "cryptography"
  sources := [
    { paper := GoldreichMicaliWigderson1991, theorem := unverified,
      locator := unverified },
    { paper := Goldreich1998Fragments, theorem := "Theorem 4.4.10, with Definition 4.3.8",
      locator := "Section 4.3.3 (Definition 4.3.8, pp. 151–152) and Section 4.4.3 \
        (Theorem 4.4.10 and the remark after it, pp. 175–176) of the posted draft of \
        February 27, 1998" }
  ]
  theorems := [
    Cslib.Crypto.NonuniformOneWay.exists_zkProof_of_mem_NP,
    Cslib.Crypto.NonuniformOneWay.exists_zkProof_of_npRelation
  ]
  scope := "From any nonuniformly one-way function, every language L in NP and every \
    NPRelation R admits a sequentially amplified ZKProof system (adapted masked-3SAT \
    protocol) with soundness (1/3)^(n+1), NegligibleSoundness, and auxiliary-input zero \
    knowledge in family-indexed, unbounded-auxiliary-input, and Goldreich instance-indexed \
    forms; the relation version preserves R's native witnesses via a Levin reduction. \
    Theorem 4.4.10 assumes a commitment scheme with nonuniform secrecy, which the remark after \
    it obtains from nonuniformly one-way functions. Of the three forms, only the instance-indexed \
    one, InstanceAuxiliaryInputZeroKnowledge, follows the indexing and clocks of Definition \
    4.3.8; it ranges over valid witnesses of polynomially bounded length in place of every \
    prover input that meets the completeness condition. The other two are novel to this \
    library and imply it."

register_result "gkst-pir-to-smooth-code" where
  title := "Smooth codes from private information retrieval schemes"
  topic := "cryptography"
  sources := [
    { paper := GoldreichKarloffSchulmanTrevisan2006, theorem := "Lemma 7.1",
      locator := "Section 7.1, pp. 19–20 of ECCC TR01-080" },
    { paper := KerenidisDeWolf2004, theorem := "Lemma 3",
      locator := "Appendix B, p. 16 of arXiv:quant-ph/0208062v2" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PIR.card_smoothPos_le,
    Cslib.Crypto.Protocols.PIR.card_smoothPos_le_six_mul,
    Cslib.Crypto.Protocols.PIR.smoothCode_zero,
    Cslib.Crypto.Protocols.PIR.smoothCode_add,
    Cslib.Crypto.Protocols.PIR.isSmoothDecoder_smoothDecoder,
    Cslib.Crypto.Protocols.PIR.isSmoothDecoder_smoothDecoder_two,
    Cslib.Crypto.Protocols.PIR.decodeLaw_smoothDecoder_of_isPrivate,
    Cslib.Crypto.Protocols.PIR.isSmoothDecoder_smoothDecoder_of_isPrivate,
    Cslib.Crypto.Protocols.PIR.smoothDecoder_eq_of_predetermined,
    Cslib.Crypto.Protocols.PIR.card_mul_sq_le_card_answer_sub_one_of_statPrivate,
    Cslib.Crypto.Protocols.PIR.card_mul_sq_le_card_answer_sub_one_of_isPrivate
  ]
  scope := "One-round k-server PIR schemes P over finite server and query sets S, Q (with \
    arbitrary retained-state type R and answer type A). Replicating each (s, q) entry \
    max 1 ⌈p₀(s, q) · |S| · |Q|⌉₊ times produces smoothCode P i₀ of length at most \
    (|S| + 1) · |S| · |Q| (≤ 6 |Q| for |S| = 2) together with a non-adaptive decoder \
    smoothDecoder P i₀ that is (|S|, |S| + 1, ε - |S| · δ / 2)-smooth under pairwise δ-statistical \
    privacy (CloseTo) and recovery probability ≥ 1/2 + ε, specializing to (2, 3, ε - δ) for two \
    servers and preserving the exact output law under perfect privacy (δ = 0). Includes additive \
    linearity preservation (smoothCodeAddHom), predetermined answer-coordinate invariance \
    (smoothDecoder_eq_of_predetermined), and the noisy / statistically-private single-server \
    answer-size bound |ι| · (ε - δ / 2)² ≤ |A| - 1 via OneQuery.lean. Expected reads coincide with \
    query probability because distinct slots query distinct servers; neither machine runtime nor \
    fair-coin simulation of rational unifFin draws is certified."

register_result "nash-existence" where
  title := "Nash's theorem: every finite game has a mixed Nash equilibrium"
  topic := "game theory"
  sources := [
    { paper := Nash1951, theorem := "Theorem 1", locator := "p. 288" },
    { paper := Roughgarden2013CS364A, theorem := unverified,
      locator := "Lecture 13, Section 3.3, p. 5" }
  ]
  theorems := [
    Cslib.GameTheory.CostGame.exists_isMixedNash
  ]
  scope := "Finite cost-minimization games: finitely many players, each with a finite nonempty \
    set of pure strategies and real-valued costs. A mixed Nash equilibrium is a profile of \
    probability vectors under which no player lowers its expected cost under the product \
    distribution by a pure deviation. Proved by Brouwer's theorem on products of simplices, \
    itself derived from the hypergrid Sperner lemma. Nonconstructive: no algorithm or \
    complexity bound."

register_result "correlated-equilibrium-hierarchy" where
  title := "Pure Nash, mixed Nash, correlated and coarse correlated equilibria are nested"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2013CS364A, theorem := unverified,
      locator := "Lecture 13, Section 3 and Figure 2; Lecture 18, Section 1" }
  ]
  theorems := [
    Cslib.GameTheory.CostGame.isCorrelatedEquilibrium_iff,
    Cslib.GameTheory.CostGame.IsPureNash.isCorrelatedEquilibrium,
    Cslib.GameTheory.CostGame.IsMixedNash.isCorrelatedEquilibrium,
    Cslib.GameTheory.CostGame.IsCorrelatedEquilibrium.isCoarseCorrelatedEquilibrium,
    Cslib.GameTheory.CostGame.exists_isCorrelatedEquilibrium
  ]
  scope := "Finite cost-minimization games and finitely supported distributions on profiles. \
    Correlated equilibria are defined by switching functions and shown equivalent to the \
    conditional form. Strictness of the inclusions is checked on examples in the test suite \
    (traffic light, Rock-Paper-Scissors), not stated as library theorems. Swap regret and \
    convergence of learning dynamics are not covered."

register_result "swap-regret-approx-ce" where
  title := "Approximate Correlated Equilibrium via Swap Regret"
  topic := "game theory"
  sources := [
    { paper := BlumMansour2007, theorem := "Theorem 3 and Corollary 7",
      locator := "pp. 1311, 1313" },
    { paper := Roughgarden2013CS364A, theorem := unverified,
      locator := "Lecture 18, Section 1" }
  ]
  theorems := [
    Cslib.GameTheory.CostGame.timeAverage_productDist_isApproxCorrelatedEquilibrium,
    Cslib.GameTheory.CostGame.blumMansourDynamics_eq_blumMansourProb,
    Cslib.GameTheory.CostGame.blumMansour_isApproxCorrelatedEquilibrium
  ]
  scope := "Finite cost-minimization games under full-information expected-cost play over a \
    fixed known finite horizon T > 0. Shows that swap regret at most R i yields an (R i / T)-\
    approximate correlated equilibrium, explicitly constructs the coupled multi-player \
    Blum–Mansour trajectory blumMansourDynamics G T (with Hedge learning rate \
    √(m_i ln m_i / T)), and proves slack 2 √(m_i ln m_i / T) when costs lie in [-1, 1], \
    m_i ≥ 2, and T ≥ m_i ln m_i. Does not cover anytime dynamics, sampled play, last-iterate \
    convergence, or native running time."

register_result "nash-existence-bimatrix" where
  title := "Every bimatrix game has a Nash equilibrium"
  topic := "game theory"
  sources := [
    { paper := Nash1951, theorem := "Theorem 1", locator := "p. 288" }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixGame.exists_isNash
  ]
  scope := "Real payoff matrices over finite nonempty strategy sets, with no nondegeneracy \
    assumption; derived from the n-player theorem. Nonconstructive."

register_result "two-player-nash-ppad" where
  title := "Two-player rational Nash equilibrium is in PPAD"
  topic := "game theory"
  sources := [
    { paper := Papadimitriou1994PPAD, theorem := unverified, locator := unverified },
    { paper := Shapley1974, theorem := unverified, locator := unverified },
    { paper := LemkeHowson1964, theorem := unverified, locator := unverified },
    { paper := vonStengel2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixCode.BimatrixNash_mem_PPAD,
    Cslib.GameTheory.BimatrixCode.BimatrixNash_mem_TFNP,
    Cslib.GameTheory.BimatrixCode.BimatrixNash_isTotalSearch,
    Cslib.GameTheory.BimatrixCode.BimatrixNash_searchReducible_EndOfLine,
    Cslib.GameTheory.BimatrixCode.BimatrixNash.isNash
  ]
  scope := "Two-player games presented as pairs of rational payoff lists under encBimatrix. \
    For well-formed nonempty m × n games, BimatrixNash asks for a canonical rational mixed Nash \
    equilibrium encoded by encWitness within explicit bit-length bound 120·L³ + 400·L + 100 \
    (malformed inputs admit only []). Proved in PPAD by lexicographic perturbation, \
    Shapley-oriented Lemke–Howson pivoting, and Cramer rounding; does not prove PPAD-hardness \
    or an efficient Lemke–Howson solver."

register_result "facility-location-random-dictatorship" where
  title := "Random dictatorship is strategyproof and (2 - 2 / n)-approximate for social cost"
  topic := "game theory"
  sources := [
    { paper := AlonFeldmanProcacciaTennenholtz2010, theorem := "Theorem 3.1",
      locator := "Section 3.2 and first remark, arXiv:0907.2049v1 pp. 6–7" }
  ]
  theorems := [
    Cslib.GameTheory.FacilityLocation.randomDictatorship_isStrategyProof,
    Cslib.GameTheory.FacilityLocation.randomDictatorship_hasApproxRatio,
    Cslib.GameTheory.FacilityLocation.randomDictatorship_hasApproxRatio_two
  ]
  scope := "Any nonempty finite agent index set ι and Borel-measurable pseudometric space G \
    ([PseudoMetricSpace G] [OpensMeasurableSpace G]); slightly generalizes AFPT Theorem 3.1 \
    and its first remark from graph/metric spaces to pseudometrics. Weak group strategyproofness \
    fails on a 3-leaf star metric (Star4 in CslibFrontierTests.FacilityLocation, per §3.2 third \
    remark), and strong group strategyproofness fails on ℝ for n = 3."

register_result "facility-location-median" where
  title := "Fixed order-statistic and median mechanisms on ℝ are group strategyproof and optimal"
  topic := "game theory"
  sources := [
    { paper := ProcacciaTennenholtz2013, theorem := unverified,
      locator := "Section 3.1, pp. 18:7–18:8 (unnumbered prose)" },
    { paper := Moulin1980, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.FacilityLocation.orderStatisticMechanism_isGroupStrategyProof,
    Cslib.GameTheory.FacilityLocation.medianMechanism_isGroupStrategyProof,
    Cslib.GameTheory.FacilityLocation.lowerMedian_isOptimal,
    Cslib.GameTheory.FacilityLocation.medianMechanism_hasApproxRatio_one
  ]
  scope := "Any nonempty finite agent set ι locating a single facility on ℝ with sum-of-distances \
    social cost; orderStatisticMechanism k clamps k at |ι| - 1 when k ≥ |ι|. PT §3.1 states \
    weak group strategyproofness (attributed to Moulin 1980, uninspected here) and optimality \
    for the lower median x_((n-1)/2); the library proves the stronger IsGroupStrategyProof \
    property."

register_result "facility-location-moulin-interval" where
  title := "Moulin characterization of strategyproof location rules on closed real intervals"
  topic := "game theory"
  sources := [
    { paper := Moulin1980, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.FacilityLocation.MoulinScheme.eval_isGroupStrategyProof,
    Cslib.GameTheory.FacilityLocation.isStrategyProof_and_surjective_iff_exists_moulinScheme,
    Cslib.GameTheory.FacilityLocation.moulinScheme_of_isometry
  ]
  scope := "Finite nonempty agent set ι and compact interval Set.Icc a b (with a < b) or \
    isometric domain. Every MoulinScheme yields a deterministic onto strongly group strategyproof \
    mechanism, and every deterministic onto strategyproof mechanism coincides with \
    MoulinScheme.eval. Moulin 1980 primary paper uninspected here."

register_result "facility-location-schummer-vohra-trees" where
  title := "Schummer–Vohra characterization of strategyproof location rules on trees"
  topic := "game theory"
  sources := [
    { paper := SchummerVohra2002, theorem := "Theorem 1",
      locator := "Section 3, p. 15 of the January 2001 author preprint" }
  ]
  theorems := [
    Cslib.GameTheory.FacilityLocation.TreeEMVS.eval_isGroupStrategyProof,
    Cslib.GameTheory.FacilityLocation.isStrategyProof_and_surjective_iff_exists_treeEMVS,
    Cslib.GameTheory.FacilityLocation.isGroupStrategyProof_of_isStrategyProof_of_surjective_tree
  ]
  scope := "Any finite nonempty agent set ι and finite connected positive-weighted tree metric \
    graph (W.graph.IsTree, MetricGraph W) with Borel measurable space. Deterministic onto \
    strategyproof rules coincide with extended median voter schemes TreeEMVS and are strongly \
    group strategyproof; majority-of-3 on star3 in CslibFrontierTests.SchummerVohra shows \
    non-dictatorial rules exist. TreeEMVS represents the source's extended median voter schemes \
    by branch-winning coalitions instead of consistent path schemes. Strong group \
    strategyproofness is proved here and is not part of the source's Theorem 1."

register_result "facility-location-schummer-vohra-cycles" where
  title := "Schummer–Vohra cycle dictatorship on graphs with cycles"
  topic := "game theory"
  sources := [
    { paper := SchummerVohra2002, theorem := "Theorem 2",
      locator := "Section 4, p. 21 of the January 2001 author preprint" }
  ]
  theorems := [
    Cslib.GameTheory.FacilityLocation.exists_cycleDictator_of_isShortestCycle,
    Cslib.GameTheory.FacilityLocation.exists_cycleDictator_of_not_isAcyclic,
    Cslib.GameTheory.FacilityLocation.exists_dictatorship_of_cycleGraph
  ]
  scope := "Any finite nonempty agent set ι and finite connected positive-weighted MetricGraph W \
    with Borel measurable space. Every deterministic onto strategyproof rule acts as a dictator \
    on profiles supported on any shortest cycle (assuming ¬ W.graph.IsAcyclic) and is globally \
    dictatorial on graphs isomorphic to cycleGraph (n + 3). Triangle + Tail in \
    CslibFrontierTests.SchummerVohra shows cycle dictatorship need not extend globally. Bounded \
    milestone of Issue #4327 (arbitrary cycles and full cyclic-network characterization remain \
    open). The source's Theorem 2 covers every cycle; only shortest cycles are formalized."

/-!
## Descriptive complexity and finite model theory

Capture theorems, undecidability in the finite, 0-1 laws, logic on words, and the game and
locality methods for nondefinability. Source theorem numbers and locators are copied from the
defining modules' documentation. Refinements and remarks that those modules present as their own
are not registered.
-/

register_result "immerman-vardi" where
  title := "Immerman–Vardi: FO(LFP) captures polynomial time on ordered structures"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1986, theorem := "Theorem 1", locator := "Section 3" }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.lfpDefinable_iff_encodedLanguage_mem_P,
    Cslib.Logic.FO.Ordered.LFPDefinable.of_encodedLanguage_mem_P
  ]
  scope := "Queries over a finite relational vocabulary on canonically ordered structures Fin n \
    with n ≥ 2. Order, BIT, 0, 1 and max are canonical numeric symbols computed from n, not \
    input tables. A query is defined by one checked FO(LFP) sentence iff its language is in \
    native P under encStructure (unary cardinality, then framed truth tables); malformed \
    table shapes and universes below two are rejected."

register_result "gradel-so-horn-captures-p" where
  title := "Grädel: SO∃-Horn captures polynomial time on ordered structures with successor"
  topic := "descriptive complexity"
  sources := [
    { paper := Gradel2007, theorem := "Theorems 3.2.17–3.2.18 and Exercise 3.2.20",
      locator := "Section 3.2.3, pp. 147–148" },
    { paper := Gradel1992, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.hornDefinable_iff_encodedLanguage_mem_P,
    Cslib.Logic.FO.Ordered.HornDefinable.encodedLanguage_mem_P,
    Cslib.Logic.FO.Ordered.HornDefinable.of_encodedLanguage_mem_P
  ]
  scope := "Queries over a finite relational vocabulary on canonically ordered structures Fin n \
    with n ≥ 2. HornDefinable asks for one SO∃-Horn sentence with quantifier-free guards over \
    language (succLanguage L), supplying primitive non-wrapping successor alongside the \
    canonical numeric symbols (order, BIT, 0, 1 and max); hornDefinable_iff_exists_sentence \
    identifies this fragment with arbitrary first-order guards over language L. A query is \
    HornDefinable iff its language is in native P under encStructure; malformed table shapes \
    and universes below two are rejected."

register_result "fo-tc-nl" where
  title := "FO(TC) is contained in NL on ordered structures"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1987, theorem := "Theorem 3.1", locator := unverified },
    { paper := Immerman1988, theorem := "Corollary 3", locator := unverified },
    { paper := Szelepcsenyi1987, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.TCDefinable.encodedLanguage_mem_NL,
    Cslib.Logic.FO.Ordered.PosTCDefinable.encodedLanguage_mem_NL
  ]
  scope := "A query defined by one FO(TC) sentence over a finite relational vocabulary with the \
    canonical numeric symbols, on Fin n with n ≥ 2, is in native NL under encStructure; \
    malformed tables and cardinalities below two are rejected. Closure is reflexive \
    transitive closure on tuples of fixed width. Closures under negation are compiled \
    directly by inductive counting rather than by appeal to NL = coNL. The converse, \
    NL ⊆ FO(positive TC), is in the entry immerman-nl-capture."

register_result "immerman-nl-capture" where
  title := "Immerman: FO(TC) and FO(positive TC) capture NL on ordered structures"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1987, theorem := "Theorem 3.1", locator := unverified },
    { paper := Immerman1988, theorem := "Corollary 3", locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.tcDefinable_iff_encodedLanguage_mem_NL,
    Cslib.Logic.FO.Ordered.posTCDefinable_iff_encodedLanguage_mem_NL
  ]
  scope := "Canonically ordered finite structures over a finite relational vocabulary, with \
    universes Fin n, n ≥ 2, and numeric symbols order, BIT, zero, one and maximum computed \
    from the size. One FO(TC) sentence defines the query iff its source-only encoded language \
    (encStructure) is in native NL; positive closures suffice. Malformed table shapes and \
    universes below two are rejected."

register_result "immerman-reach-nl-complete" where
  title := "Immerman: REACH is NL-complete under ordered first-order reductions"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1999, theorem := "Theorem 3.16 and Exercise 3.20",
      locator := "Chapter 3, pp. 64–66" }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.reduces_Reach_iff_encodedLanguage_mem_NL,
    Cslib.Logic.FO.Ordered.exists_fullTupleInterpretation_Reach_of_encodedLanguage_mem_NL,
    Cslib.Logic.FO.Ordered.reach_encodedLanguage_mem_NL,
    Cslib.Logic.FO.Ordered.stReach_encodedLanguage_mem_NL,
    Cslib.Logic.FO.Ordered.reach_logSpaceComplete_NL
  ]
  scope := "Canonically ordered finite relational structures on Fin n (2 ≤ n) with built-in \
    ≤, BIT, 0, 1 and max, encoded at encStructure; native multi-tape NL with all-branches \
    halting. Reach is 0-to-max directed reachability over Language.graph (arbitrary binary \
    edge relation, self-loops permitted). Every ordered query in native NL reduces to Reach \
    by one positive-dimensional FullTupleInterpretation (hence Ordered.Reduces), and conversely \
    via positive FO(TC) pullback. Endpoint normalization covers arbitrary marked (s, t) \
    including s = t, and Reach is logspace interreducible with STCON (encSTCON). First-order \
    and quantifier-free projection refinements (≤_fop, ≤_qfp) are not formalized here."

register_result "fo-dtc-l" where
  title := "FO(DTC) is contained in L on ordered structures"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1987, theorem := "Theorem 4.2", locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.DTCDefinable.encodedLanguage_mem_L
  ]
  scope := "A query defined by one FO(DTC) sentence over a finite relational vocabulary with the \
    canonical numeric symbols, on Fin n with n ≥ 2, is in native L under encStructure; \
    malformed tables and cardinalities below two are rejected. Deterministic closure is \
    reflexive transitive closure of the deterministic reduct on tuples of fixed width, \
    nested and at any polarity. The converse, L ⊆ FO(DTC), is in the entry \
    immerman-l-capture."

register_result "immerman-l-capture" where
  title := "Immerman: FO(DTC) captures L on ordered structures"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1987, theorem := "Theorem 4.2", locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.dtcDefinable_iff_encodedLanguage_mem_L
  ]
  scope := "Canonically ordered finite structures over a finite relational vocabulary, with \
    universes Fin n, n ≥ 2, and numeric symbols order, BIT, zero, one and maximum computed \
    from the size. One FO(DTC) sentence defines the query iff its source-only encoded \
    language (encStructure) is in native L. Deterministic closure is reflexive transitive \
    closure of the deterministic reduct on tuples of fixed width. Malformed table shapes and \
    universes below two are rejected."

register_result "ordered-projection-reducibility" where
  title := "Immerman–Landau: ordered FO and QF projections compose and refine FO reductions"
  topic := "descriptive complexity"
  sources := [
    { paper := ImmermanLandau1995, theorem := "Proposition 3.7", locator := "Section 3" },
    { paper := Immerman1999, theorem := "Exercise 2.15(1)", locator := "Chapter 2, p. 36" }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.ProjectionReduces.refl,
    Cslib.Logic.FO.Ordered.ProjectionReduces.trans,
    Cslib.Logic.FO.Ordered.ProjectionReduces.reduces,
    Cslib.Logic.FO.Ordered.QFProjectionReduces.refl,
    Cslib.Logic.FO.Ordered.QFProjectionReduces.trans,
    Cslib.Logic.FO.Ordered.QFProjectionReduces.projectionReduces,
    Cslib.Logic.FO.Ordered.QFProjectionReduces.reduces
  ]
  scope := "Queries on canonically ordered relational structures Fin n with n ≥ 2. Projections \
    are positive-dimensional full-tuple interpretations whose output relations are decision \
    trees of numeric guards with constants or single signed input literals at the leaves; \
    first-order projections allow guards over order, BIT, 0, 1 and max, while quantifier-free \
    projections require quantifier-free guards over order, non-wrapping successor, 0 and max \
    without BIT. Both IsProjectionMap and IsQFProjectionMap contain the identity and are \
    closed under composition (with BIT-free quantifier-free guard pullback via \
    QFNumeric.onFullTuple); the logspace encoding lift at encStructure is proved in \
    Classes.LogSpace.FirstOrder.Ordered.Projection, and NP-completeness endpoints are in \
    immerman-sat-np-complete and ordered-np-complete-problems."

register_result "ordered-sized-graph-qfp" where
  title := "Ordered IndependentSet, Clique, and VertexCover are pairwise QF-projection equivalent"
  topic := "descriptive complexity"
  sources := [
    { paper := Karp1972, theorem := unverified, locator := unverified },
    { paper := Immerman1999, theorem := unverified, locator := unverified },
    { paper := ImmermanLandau1995, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.independentSet_qfProjectionReduces_Clique,
    Cslib.Logic.FO.Ordered.clique_qfProjectionReduces_IndependentSet,
    Cslib.Logic.FO.Ordered.independentSet_qfProjectionReduces_VertexCover,
    Cslib.Logic.FO.Ordered.vertexCover_qfProjectionReduces_IndependentSet,
    Cslib.Logic.FO.Ordered.clique_qfProjectionReduces_VertexCover,
    Cslib.Logic.FO.Ordered.vertexCover_qfProjectionReduces_Clique
  ]
  scope := "Queries on canonically ordered FO.sizedGraph structures on Fin n (2 ≤ n), where \
    target set cardinality is the cardinality of the unary relation size. Dimension-1 BIT-free \
    quantifier-free projections complement off-diagonal edges (guarding the diagonal by numeric \
    equality x = y) and complement the unary size relation; transitivity yields all six \
    pairwise QFProjectionReduces reductions."

register_result "ordered-sat-to-threesat-qfp" where
  title := "Ordered SAT reduces to ThreeSAT via a BIT-free quantifier-free projection"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1999, theorem := unverified, locator := unverified },
    { paper := ImmermanLandau1995, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_ThreeSAT,
    Cslib.Logic.FO.Ordered.isQFProjection_satToThreeSATInterpretation,
    Cslib.Logic.FO.Ordered.mem_ThreeSAT_satToThreeSATInterpretation
  ]
  scope := "Queries on canonically ordered FO.cnf structures on Fin n (2 ≤ n), where ThreeSAT \
    requires at most three literals per clause. A dimension-5 BIT-free quantifier-free \
    projection over order, non-wrapping successor, 0 and max chains positive and negative \
    literal scans with relay variables and pads unused clause tuples with two-literal \
    tautologies; each output bit reads at most one input literal. Unconditional NP-completeness \
    is in ordered-np-complete-problems."

register_result "ordered-sat-to-independent-set-qfp" where
  title := "Ordered SAT reduces to IndependentSet, Clique, and VertexCover via QF projections"
  topic := "descriptive complexity"
  sources := [
    { paper := Karp1972, theorem := unverified, locator := unverified },
    { paper := Immerman1999, theorem := unverified, locator := unverified },
    { paper := ImmermanLandau1995, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_IndependentSet,
    Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_Clique,
    Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_VertexCover,
    Cslib.Logic.FO.Ordered.isQFProjection_satToIndependentSetInterpretation,
    Cslib.Logic.FO.Ordered.mem_IndependentSet_satToIndependentSetInterpretation
  ]
  scope := "A dimension-4 BIT-free quantifier-free projection maps any canonically ordered \
    FO.cnf structure on Fin n (2 ≤ n) to an FO.sizedGraph structure partitioned into n clause \
    cliques plus one top clique with a distinguished anchor vertex and target size n + 1; \
    anchor-to-clause edges test single negated input literals and inter-clause edges enforce \
    variable consistency. Composing with the dimension-1 sizedGraph projections yields \
    QFProjectionReduces to Clique and VertexCover; unconditional NP-completeness is in \
    ordered-np-complete-problems."

register_result "ordered-sat-to-three-coloring-qfp" where
  title := "Ordered SAT reduces to simple and general 3-colorability via a QF projection"
  topic := "descriptive complexity"
  sources := [
    { paper := GareyJohnson1979, theorem := unverified, locator := unverified },
    { paper := Sipser2013, theorem := unverified, locator := unverified },
    { paper := ImmermanLandau1995, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_SimpleThreeColorable,
    Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_ThreeColorable,
    Cslib.Logic.FO.Ordered.isQFProjection_satToColoringInterpretation,
    Cslib.Logic.FO.Ordered.simpleGraph_satToColoring,
    Cslib.Logic.FO.Ordered.mem_SimpleThreeColorable_satToColoringInterpretation,
    Cslib.Logic.FO.Ordered.mem_ThreeColorable_satToColoringInterpretation
  ]
  scope := "A dimension-6 BIT-free quantifier-free projection over order, non-wrapping \
    successor, 0 and max maps any canonically ordered FO.cnf structure on Fin n (2 ≤ n) to a \
    simple loopless undirected Language.graph structure (modeling Theory.simpleGraph on all \
    inputs) using a palette triangle, literal switches, single-literal activation edges, and \
    successor-linked 3-vertex OR-gate chains. Simultaneously reduces Ordered.SAT to \
    Ordered.SimpleThreeColorable and Ordered.ThreeColorable; unconditional NP-completeness is \
    in ordered-np-complete-problems."

register_result "ordered-np-queries-fagin-and-logspace" where
  title := "Ordered NP benchmark queries lie in ESO and native NP with logspace gadget reductions"
  topic := "descriptive complexity"
  sources := [
    { paper := Fagin1974, theorem := unverified, locator := unverified },
    { paper := Immerman1999, theorem := unverified, locator := unverified },
    { paper := ImmermanLandau1995, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.ESODefinable.of_definable,
    Cslib.Logic.FO.Ordered.sat_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.threeSAT_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.threeColorable_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.simpleThreeColorable_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.independentSet_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.clique_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.vertexCover_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.sat_logSpaceReducible_ThreeSAT,
    Cslib.Logic.FO.Ordered.sat_logSpaceReducible_SimpleThreeColorable,
    Cslib.Logic.FO.Ordered.sat_logSpaceReducible_ThreeColorable,
    Cslib.Logic.FO.Ordered.sat_logSpaceReducible_IndependentSet,
    Cslib.Logic.FO.Ordered.sat_logSpaceReducible_Clique,
    Cslib.Logic.FO.Ordered.sat_logSpaceReducible_VertexCover
  ]
  scope := "Pushing unordered existential second-order sentences forward along LHom.sumInl \
    places Ordered.SAT, Ordered.ThreeSAT, Ordered.ThreeColorable, Ordered.SimpleThreeColorable, \
    Ordered.IndependentSet, Ordered.Clique, and Ordered.VertexCover in Ordered.ESODefinable and \
    in native NP under encStructure via the ordered Fagin verifier; lifting their BIT-free \
    quantifier-free projections yields deterministic LogSpaceReducible reductions at \
    encStructure. Full ≤_qfp, ≤_fop, ≤_fo and encStructure NP-completeness is in \
    immerman-sat-np-complete and ordered-np-complete-problems."

register_result "ordered-eso-qfp-grounding" where
  title := "Ordered relational ESO sentences ground to SAT via BIT-free QF projections"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1999, theorem := unverified, locator := unverified },
    { paper := ImmermanLandau1995, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.qfProjectionReduces_SAT_of_orderSentence,
    Cslib.Logic.ESO.Sentence.isQFProjection_groundQFInterpretation,
    Cslib.Logic.ESO.Sentence.satisfiable_tupleStructure_groundQFInterpretation_iff,
    Cslib.Logic.ESO.Sentence.mem_SAT_groundQFInterpretation
  ]
  scope := "For any relational language L and existential second-order sentence Φ over \
    L.sum ESO.orderLanguage, groundQFInterpretation compiles Φ uniformly into a positive-dimension \
    FullTupleInterpretation L FO.cnf certified by IsQFProjection (BIT-free, over qfNumericLanguage \
    with ≤, non-wrapping succ, 0, and max). Ground tags are encoded via binary {0, max} prefixes \
    (MatchBinaryTag), inactive tuples carry self-tautologies, and strict order guards compile to \
    numeric order comparisons on Fin M.size (2 ≤ M.size), yielding QFProjectionReduces K \
    Ordered.SAT without machine or complexity imports."

register_result "immerman-sat-np-complete" where
  title := "Immerman: ordered SAT is NP-complete under BIT-free quantifier-free projections"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1999, theorem := unverified, locator := unverified },
    { paper := ImmermanLandau1995, theorem := unverified, locator := unverified },
    { paper := Fagin1974, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.qfProjectionReduces_SAT_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.projectionReduces_SAT_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.reduces_SAT_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.qfProjectionReduces_SAT_of_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.esoDefinable_iff_qfProjectionReduces_SAT,
    Cslib.Logic.FO.Ordered.sat_npComplete,
    Cslib.Logic.FO.Ordered.cnf_polyTimeReducible_orderedSAT,
    Cslib.Logic.FO.Ordered.orderedSAT_polyTimeReducible_cnf
  ]
  scope := "Queries on canonically ordered finite relational structures Fin n (2 ≤ n) over a \
    finite relational vocabulary v, with source-only encodings at encStructure. Combining the \
    ordered Fagin tableau sentence on a polynomial power structure with BIT-free quantifier-free \
    projection grounding (ordered-eso-qfp-grounding) characterizes native NP membership at \
    encStructure and ESODefinable uniformly by QFProjectionReduces (≤_qfp), ProjectionReduces \
    (≤_fop), or Ordered.Reduces (≤_fo) to Ordered.SAT. At the machine level, cnfToOrdered gives an \
    explicit polynomial-time reduction from Complexity.SAT (encCNF) to Ordered.SAT (encStructure), \
    establishing NPComplete encStructure and bidirectional PolyTimeReducible equivalence."

register_result "ordered-np-complete-problems" where
  title := "Ordered ThreeSAT, 3-coloring, IndependentSet, Clique, and VertexCover are NP-complete"
  topic := "descriptive complexity"
  sources := [
    { paper := Karp1972, theorem := unverified, locator := unverified },
    { paper := GareyJohnson1979, theorem := unverified, locator := unverified },
    { paper := Immerman1999, theorem := unverified, locator := unverified },
    { paper := ImmermanLandau1995, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.qfProjectionReduces_ThreeSAT_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.qfProjectionReduces_SimpleThreeColorable_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.qfProjectionReduces_ThreeColorable_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.qfProjectionReduces_IndependentSet_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.qfProjectionReduces_Clique_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.qfProjectionReduces_VertexCover_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.threeSAT_npComplete,
    Cslib.Logic.FO.Ordered.simpleThreeColorable_npComplete,
    Cslib.Logic.FO.Ordered.threeColorable_npComplete,
    Cslib.Logic.FO.Ordered.independentSet_npComplete,
    Cslib.Logic.FO.Ordered.clique_npComplete,
    Cslib.Logic.FO.Ordered.vertexCover_npComplete,
    Cslib.Logic.FO.Ordered.threeSAT_polyTimeReducible_orderedThreeSAT,
    Cslib.Logic.FO.Ordered.orderedThreeSAT_polyTimeReducible_threeSAT,
    Cslib.Logic.FO.Ordered.threeColoring_polyTimeReducible_orderedSimpleThreeColorable,
    Cslib.Logic.FO.Ordered.orderedSimpleThreeColorable_polyTimeReducible_threeColoring,
    Cslib.Logic.FO.Ordered.threeColoring_polyTimeReducible_orderedThreeColorable,
    Cslib.Logic.FO.Ordered.orderedThreeColorable_polyTimeReducible_threeColoring,
    Cslib.Logic.FO.Ordered.independentSet_polyTimeReducible_orderedIndependentSet,
    Cslib.Logic.FO.Ordered.orderedIndependentSet_polyTimeReducible_independentSet,
    Cslib.Logic.FO.Ordered.clique_polyTimeReducible_orderedClique,
    Cslib.Logic.FO.Ordered.orderedClique_polyTimeReducible_clique,
    Cslib.Logic.FO.Ordered.vertexCover_polyTimeReducible_orderedVertexCover,
    Cslib.Logic.FO.Ordered.orderedVertexCover_polyTimeReducible_vertexCover
  ]
  scope := "Composing ≤_qfp-hardness of Ordered.SAT with the BIT-free quantifier-free gadget \
    projections and downward NP closure under Ordered.Reduces characterizes native NP membership \
    at encStructure by QFProjectionReduces, ProjectionReduces, and Ordered.Reduces to each of \
    Ordered.ThreeSAT, Ordered.SimpleThreeColorable, Ordered.ThreeColorable, \
    Ordered.IndependentSet, Ordered.Clique, and Ordered.VertexCover. Lifting to encStructure and \
    combining with Cook–Levin / Karp hardness proves NPComplete encStructure for all six \
    queries and explicit bidirectional PolyTimeReducible bridges to Complexity.ThreeSAT, \
    Complexity.ThreeColoring, Complexity.IndependentSet, Complexity.Clique, and \
    Complexity.VertexCover."

register_result "trakhtenbrot" where
  title := "Trakhtenbrot: finite satisfiability is undecidable"
  topic := "descriptive complexity"
  sources := [
    { paper := Trakhtenbrot1950, theorem := unverified, locator := unverified },
    { paper := Libkin2004, theorem := "Theorem 9.2 and Corollary 9.3", locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.RawFormula.not_computablePred_finSat,
    Cslib.Logic.FO.RawFormula.not_rePred_finValid,
    Cslib.Logic.FO.RawFormula.not_rePred_not_finSat,
    Cslib.Logic.FO.RawFormula.exists_finValid_not_of_rePred,
    Cslib.Logic.FO.RawFormula.exists_finValid_unprovable
  ]
  scope := "Library-local raw relational formulas (RawFormula, with equality and relation \
    symbols named by natural numbers), not Mathlib L.Sentence; the reduction uses unboundedly \
    many symbols of arity at most three. FinSat asks for some, FinValid for every, finite \
    nonempty structure and assignment. Decidability is Mathlib's ComputablePred/REPred; the \
    reduction is from halting of Mathlib's Code.evaln, not from Turing machine runs. \
    Corollaries: every r.e. set of finitely valid formulas misses one, so no sound proof \
    system with a decidable proof relation proves every finitely valid formula. The \
    sharpening to a fixed vocabulary containing a relation symbol of arity at least two and \
    the transfer to Mathlib sentences are separate entries."

register_result "trakhtenbrot-binary" where
  title := "Trakhtenbrot's theorem for a vocabulary with a relation symbol of arity at least two"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Theorem 9.2 and Corollary 9.3", locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.RawFormula.not_exists_computable_finSat_of_mem,
    Cslib.Logic.FO.RawFormula.not_exists_rePred_finValid_of_mem,
    Cslib.Logic.FO.RawFormula.exists_isSentenceOver_finValid_not_of_rePred,
    Cslib.Logic.FO.RawFormula.exists_isSentenceOver_finValid_unprovable
  ]
  scope := "For every vocabulary σ ⊆ ℕ × ℕ of (symbol, arity) pairs containing a symbol of \
    arity at least two, no computable procedure is correct for finite satisfiability on the \
    raw sentences over σ, and the finitely valid sentences over σ are not r.e.; hence every \
    r.e. set of finitely valid sentences misses one over σ, and no sound proof system with a \
    decidable proof relation proves them all. Libkin's Theorem 9.2 and Corollary 9.3 state \
    the binary case; higher arities pad binary atoms by repeating the second argument. Raw \
    library-local syntax with finite nonempty models; the form for Mathlib's L.Sentence is \
    the entry trakhtenbrot-sentence."

register_result "trakhtenbrot-sentence" where
  title := "Trakhtenbrot's theorem for Mathlib sentences"
  topic := "descriptive complexity"
  sources := [
    { paper := Trakhtenbrot1950, theorem := unverified, locator := unverified },
    { paper := Libkin2004, theorem := "Theorem 9.2 and Corollary 9.3", locator := unverified }
  ]
  theorems := [
    FirstOrder.Language.Sentence.rePred_finSat,
    FirstOrder.Language.Sentence.not_computablePred_finSat,
    FirstOrder.Language.Sentence.not_rePred_finValid,
    FirstOrder.Language.Sentence.exists_finValid_unprovable
  ]
  scope := "Mathlib L.Sentence over a relational language with finitely many relation \
    symbols; the negative results take a relation symbol of arity at least two (Libkin's \
    Theorem 9.2 and Corollary 9.3 state the binary case; higher arities pad binary atoms by \
    repeating the second argument). Sentences are coded by primcodableRaw, a scoped \
    instance, independent of the symbol encoding up to primitive recursive equivalence. \
    FinSat and FinValid quantify over finite nonempty structures. Function symbols and \
    infinite vocabularies are not covered; the decidable monadic converse and dichotomy are \
    in trakhtenbrot-dichotomy."

register_result "trakhtenbrot-dichotomy" where
  title := "Trakhtenbrot–Löwenheim: the decidability dichotomy for finite satisfiability"
  topic := "descriptive complexity"
  sources := [
    { paper := Trakhtenbrot1950, theorem := unverified, locator := unverified },
    { paper := Lowenheim1915, theorem := unverified, locator := unverified },
    { paper := Libkin2004, theorem := "Theorem 9.2 and Corollary 9.3", locator := unverified }
  ]
  theorems := [
    FirstOrder.Language.Sentence.computablePred_finSat_iff,
    FirstOrder.Language.Sentence.computablePred_finValid_iff,
    FirstOrder.Language.Sentence.rePred_finValid_iff,
    FirstOrder.Language.Sentence.rePred_not_finSat_iff,
    FirstOrder.Language.Sentence.computablePred_finSat_of_monadic,
    FirstOrder.Language.Sentence.computablePred_finValid_of_monadic
  ]
  scope := "Mathlib L.Sentence over a relational language with finitely many relation \
    symbols, coded by primcodableRaw. Finite satisfiability and finite validity (over \
    finite nonempty structures) are decidable—and finite validity and finite \
    unsatisfiability are r.e.—if and only if every relation symbol has arity at most one \
    (allowing both unary and nullary symbols). On the monadic side, finite satisfiability \
    and finite validity are primitive recursive by checking RawFormula.SatOnFin below the \
    explicit bound max q 1 * 2 ^ k proved in monadic-small-model (Löwenheim is cited for \
    decidability of the monadic class only). Function symbols and infinite vocabularies \
    are not covered."

register_result "zero-one-law-graphs" where
  title := "Glebskiĭ–Kogan–Liogon'kiĭ–Talanov and Fagin: the 0-1 law for random graphs"
  topic := "descriptive complexity"
  sources := [
    { paper := GlebskiiKoganLiogonkiiTalanov1969, theorem := unverified,
      locator := unverified },
    { paper := Fagin1976, theorem := unverified, locator := unverified },
    { paper := Libkin2004, theorem := unverified, locator := "Chapter 12" }
  ]
  theorems := [
    Cslib.Logic.FO.graph.zero_one_law,
    Cslib.Logic.FO.graph.tendsto_randomGraphProb_one_iff,
    Cslib.Logic.FO.graph.tendsto_randomGraphProb_zero_iff,
    Cslib.Logic.FO.graph.not_exists_sentence_of_not_tendsto,
    Cslib.Logic.FO.graph.not_exists_sentence_even_card,
    Cslib.Logic.FO.graph.not_definable_even_card,
    Cslib.Logic.FO.graph.not_exists_sentence_evenEdges
  ]
  scope := "First-order sentences of Mathlib's language of graphs under the uniform labelled \
    random graph G(n, 1/2) on Fin n. The limit probability is 1 exactly for the \
    consequences of the theory of the random graph and 0 exactly when the negation is one. \
    Consequences: even vertex count and even edge count are not first-order definable. \
    Constant edge probabilities 0 < p < 1 are covered by the entry zero-one-law-binomial; \
    edge probabilities depending on n and unlabelled random graphs are not covered."

register_result "zero-one-law-rado" where
  title := "The Rado graph and the almost-sure theory of G(n, 1/2)"
  topic := "descriptive complexity"
  sources := [
    { paper := Fagin1976, theorem := unverified, locator := unverified },
    { paper := Rado1964, theorem := unverified, locator := unverified },
    { paper := Libkin2004, theorem := unverified, locator := "Section 12.3" }
  ]
  theorems := [
    Cslib.Logic.FO.graph.tendsto_randomGraphProb_one_iff_radoGraph,
    Cslib.Logic.FO.graph.tendsto_randomGraphProb_zero_iff_radoGraph,
    Cslib.Logic.FO.graph.nonempty_iso_radoGraph,
    Cslib.Logic.FO.graph.nonempty_embedding_radoGraph,
    Cslib.Logic.FO.graph.nonempty_compl_iso_radoGraph
  ]
  scope := "A sentence of the language of graphs holds almost surely in G(n, 1/2) iff it holds \
    in the Rado graph SimpleGraph.radoGraph on ℕ, and almost never otherwise. Structure \
    theory for countable simple graphs: uniqueness among graphs with every extension \
    property, universality for induced embeddings, and self-complementarity."

register_result "zero-one-law-binomial" where
  title := "The 0-1 law for G(n, p) with constant edge probability"
  topic := "descriptive complexity"
  sources := [
    { paper := AlonSpencer2016, theorem := unverified, locator := unverified },
    { paper := Fagin1976, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.graph.binomialRandom_zero_one_law,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_one_iff,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_zero_iff,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_one_iff_radoGraph,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_zero_iff_radoGraph,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_one_iff_tendsto_randomGraphProb,
    Cslib.Logic.FO.graph.not_exists_sentence_of_not_tendsto_binomialRandom
  ]
  scope := "First-order sentences of Mathlib's language of graphs under Mathlib's binomial \
    random graph SimpleGraph.binomialRandom (Fin n) p, labelled, for a fixed real \
    0 < p < 1. The limit probability is 1 exactly for the consequences of the theory of the \
    random graph, equivalently for the sentences true in the Rado graph, so the almost-sure \
    sentences are those of G(n, 1/2) for every such p. At p = 0 and p = 1 the graph is \
    empty or complete and this characterization fails. Edge probabilities depending on n, \
    other vocabularies and unlabelled random graphs are not covered."

register_result "zero-one-law-relational" where
  title := "The 0-1 law for finite relational vocabularies"
  topic := "descriptive complexity"
  sources := [
    { paper := GlebskiiKoganLiogonkiiTalanov1969, theorem := unverified,
      locator := unverified },
    { paper := Fagin1976, theorem := unverified, locator := unverified },
    { paper := Libkin2004, theorem := unverified, locator := "Chapter 12" }
  ]
  theorems := [
    Cslib.Logic.FO.Relational.zero_one_law,
    Cslib.Logic.FO.Relational.tendsto_sentenceProb_one_iff,
    Cslib.Logic.FO.Relational.tendsto_sentenceProb_zero_iff,
    Cslib.Logic.FO.Relational.not_exists_sentence_even_card,
    Cslib.Logic.FO.Relational.not_definable_even_card,
    Cslib.Logic.FO.Relational.bernoulliStructure_zero_one_law,
    Cslib.Logic.FO.Relational.tendsto_sentenceProb_bernoulliStructure_one_iff,
    Cslib.Logic.FO.Relational.tendsto_sentenceProb_bernoulliStructure_zero_iff,
    Cslib.Logic.FO.Relational.tendsto_sentenceProb_bernoulliStructure_one_iff_uniformStructure,
    Cslib.Logic.FO.Relational.not_exists_sentence_of_not_tendsto_bernoulliStructure
  ]
  scope := "Relational languages with finitely many relation symbols, none nullary, under the \
    uniform measure on L-structures on {0, …, n - 1}. The limit is 1 exactly for the \
    consequences of the extension theory and 0 exactly when the negation is one. The law \
    fails with a nullary symbol. For Language.graph the measure is uniform on directed \
    graphs with loops, so this is not the G(n, 1/2) law. The sources cover this uniform law, \
    in which every atomic fact has probability 1/2 (Fagin1976). The bernoulliStructure \
    theorems extend it to a constant probability 0 < p R < 1 for each relation symbol R, with \
    the same almost-sure sentences for every such p. That extension is an adaptation of \
    Fagin's proof made here; no primary source for it was found, and none of the listed \
    sources is claimed for it. With p R equal to 0 or 1 the characterization by the \
    extension theory fails, although the 0-1 law still holds by replacing the symbol with \
    ⊥ or ⊤ (it is a.s. empty or full); that reduction is not formalized. Unlabelled \
    structures and probabilities depending on n are not covered."

register_result "kolaitis-vardi-zero-one-law" where
  title := "Kolaitis–Vardi: the 0-1 law for finite-variable infinitary logic L^k_∞ω"
  topic := "descriptive complexity"
  sources := [
    { paper := KolaitisVardi1992, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.infinitary_zero_one_law_of_finset,
    Cslib.Logic.FO.graph.isPebbleBackAndForth_of_satisfies_extensionAxiom_lt,
    Cslib.Logic.FO.graph.binomialRandom_infinitary_zero_one_law,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_infinitary_one_iff_radoGraph,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_infinitary_zero_iff_radoGraph,
    Cslib.Logic.FO.graph.randomGraph_infinitary_zero_one_law,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_infinitary_one_iff_tendsto_randomGraphProb,
    Cslib.Logic.FO.graph.not_exists_infinitaryFormula_of_not_tendsto_binomialRandom,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_connected,
    Cslib.Logic.FO.Relational.isPebbleBackAndForth_of_hasExtension_lt,
    Cslib.Logic.FO.Relational.uniformStructure_infinitary_zero_one_law,
    Cslib.Logic.FO.Relational.bernoulliStructure_infinitary_zero_one_law,
    Cslib.Logic.FO.Relational.tendsto_infinitaryProb_bernoulliStructure_one_iff_model,
    Cslib.Logic.FO.Relational.tendsto_infinitaryProb_bernoulliStructure_zero_iff_model,
    Cslib.Logic.FO.Relational.tendsto_infinitaryProb_bernoulliStructure_one_iff_uniformStructure,
    Cslib.Logic.FO.Relational.not_exists_infinitaryFormula_even_card
  ]
  scope := "Closed formulas of the k-variable infinitary logic L^k_∞ω (at any disjunction index \
    universe w and any quantifier depth) over Mathlib's language of graphs under G(Fin n, p) \
    (0 < p < 1) and G(n, 1/2), and over finite relational vocabularies with no nullary symbols \
    under uniformStructure n and bernoulliStructure p n (0 < p R < 1). Because moving one of k \
    pebbles leaves at most k - 1 fixed pebbles, the finitely many extension axioms of arity \
    strictly below k make PartialIsoOn a k-pebble back-and-forth invariant. In G(Fin n, p), the \
    limit is 1 iff the sentence holds in SimpleGraph.radoGraph (independent of p), yielding \
    almost-sure connectivity as a corollary of L^3_∞ω definability. KolaitisVardi1992 is cited \
    for the uniform L^k_∞ω 0-1 law; the constant-probability G(Fin n, p) and per-symbol \
    bernoulliStructure extensions combine their pebble-game argument with the repository's \
    constant-probability extension bounds. Fixed-point 0-1 laws (not needed separately once \
    FO(LFP) embeds into L^ω_∞ω, which is not yet formalized), probabilities depending on n, and \
    unlabelled structures are not covered."

register_result "buchi-elgot-trakhtenbrot" where
  title := "Büchi–Elgot–Trakhtenbrot: MSO-definable languages are the regular languages"
  topic := "descriptive complexity"
  sources := [
    { paper := Buchi1960, theorem := unverified, locator := unverified },
    { paper := Elgot1961, theorem := unverified, locator := unverified },
    { paper := Libkin2004, theorem := "Theorem 7.21", locator := unverified },
    { paper := Thomas1997, theorem := unverified, locator := "Section 3" }
  ]
  theorems := [
    Cslib.Logic.WordMSO.definable_iff_isRegular,
    Cslib.Logic.WordMSO.definable_of_isRegular
  ]
  scope := "Languages of finite words over a finite alphabet; MSO over word structures with \
    positions, <, letter predicates and set variables, including the empty word. Regularity \
    is Mathlib's Language.IsRegular. The direction MSO ⇒ regular, proved in the ToRegular \
    module, holds over every alphabet."

register_result "fo-mso-separation" where
  title := "FO[<] is strictly weaker than MSO on finite words"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Corollary 7.27", locator := unverified }
  ]
  theorems := [
    Cslib.Logic.WordMSO.not_foDefinable_even,
    Cslib.Logic.WordMSO.exists_definable_not_foDefinable,
    Cslib.Logic.WordMSO.exists_isRegular_not_foDefinable,
    Cslib.Logic.WordMSO.not_exists_sentence_language_eq_even
  ]
  scope := "Even length is MSO-definable and regular but not definable in FO[<] with letter \
    predicates (no BIT), over any nonempty alphabet; over one letter this is the \
    first-order half of Libkin's Corollary 7.27 for (aa)*. Over the empty alphabet every \
    language is first-order definable."

register_result "star-free-fo" where
  title := "Star-free languages are first-order definable; even length is not star-free"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Theorem 7.26 and Corollary 7.27",
      locator := unverified },
    { paper := McNaughtonPapert1971, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Language.IsStarFree.foDefinable,
    Cslib.Logic.WordMSO.not_isStarFree_even,
    Cslib.Logic.WordMSO.exists_isRegular_not_isStarFree
  ]
  scope := "The direction star-free ⇒ FO[<] of McNaughton–Papert, over any alphabet, possibly \
    infinite. With the FO[<] separation it gives that even length (over one letter, (aa)*) \
    is regular but not star-free, over any nonempty alphabet. The remark that FO ⇒ \
    star-free fails over an infinite alphabet is not registered."

register_result "mcnaughton-papert" where
  title := "McNaughton–Papert: first-order definable equals star-free on finite words"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Theorem 7.26",
      locator := "second half of the proof, pp. 128–129" },
    { paper := McNaughtonPapert1971, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.WordMSO.foDefinable_iff_isStarFree,
    Cslib.Logic.WordMSO.FODefinable.isStarFree
  ]
  scope := "Languages of finite words over a finite alphabet, FO[<] with letter predicates and \
    no BIT. The direction FO ⇒ star-free needs the finite alphabet; the proof adapts \
    Libkin's induction on quantifier rank."

register_result "ehrenfeucht-fraisse" where
  title := "The Ehrenfeucht–Fraïssé theorem"
  topic := "descriptive complexity"
  sources := [
    { paper := Ehrenfeucht1961, theorem := unverified, locator := unverified },
    { paper := Fraisse1954, theorem := unverified, locator := unverified },
    { paper := Libkin2004, theorem := unverified, locator := "Chapter 3" },
    { paper := EbbinghausFlum1999, theorem := unverified, locator := "Chapter 2" }
  ]
  theorems := [
    Cslib.Logic.FO.duplicatorWins_iff_forall_realize_iff,
    Cslib.Logic.FO.duplicatorWins_iff_forall_formula,
    Cslib.Logic.FO.duplicatorWins_iff_forall_sentence,
    Cslib.Logic.FO.duplicatorWins_of_forall_realize_iff,
    Cslib.Logic.FO.exists_finite_quantifierRank_le_realize_iff,
    Cslib.Logic.FO.elementarilyEquivalent_iff_forall_duplicatorWins
  ]
  scope := "Mathlib first-order languages with finitely many relation symbols; structures may \
    be finite or infinite. Duplicator wins the n-round game from tuples a, b iff they \
    satisfy the same formulas of quantifier rank at most n. The equivalences need \
    L.IsRelational; the Hintikka direction needs only finitely many relation symbols. Also: \
    finitely many rank-n formulas up to equivalence, and elementary equivalence as winning \
    every finite game."

register_result "pebble-games-fo-k" where
  title := "The pebble-game characterization of finite-variable logic FO^k"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1999, theorem := "Theorem 6.10", locator := "Section 6.1, p. 123" },
    { paper := Libkin2004, theorem := "Theorem 11.5, Proposition 11.8 and Corollary 11.9",
      locator := "Section 11.2, pp. 216–218" }
  ]
  theorems := [
    Cslib.Logic.FO.pebbleWins_iff_forall_realize_iff,
    Cslib.Logic.FO.pebbleWinsForever_iff_forall_realize_iff
  ]
  scope := "Mathlib first-order languages with finitely many relation symbols; k-variable \
    formulas reuse variables and have equality and relational atoms. Duplicator wins the \
    n-round k-pebble game from a position (S, a, b) iff a and b satisfy the same FO^k formulas \
    of quantifier rank at most n with free variables in S, for arbitrary structures; the \
    infinite game corresponds to all FO^k formulas on finite structures. Positions are total \
    assignments, so for k > 0 the statements are vacuous on empty structures. Libkin states \
    the results for the infinitary logic L^k_∞ω on finite structures; the remark before \
    Proposition 11.8 reduces rank n to FO^k."

register_result "bijective-pebble-games-c-k" where
  title := "The bijective pebble-game characterization of finite-variable counting logic C^k"
  topic := "descriptive complexity"
  sources := [
    { paper := CaiFurerImmerman1992, theorem := "Theorem 4.5",
      locator := "Section 4.1; the round-indexed form is in the proof of Theorem 5.2" },
    { paper := Hella1996, theorem := unverified, locator := unverified },
    { paper := Immerman1999, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.bijPebbleWins_iff_forall_realize_iff,
    Cslib.Logic.FO.bijPebbleWinsForever_iff_forall_realize_iff
  ]
  scope := "Mathlib first-order languages with finitely many relation symbols, finite \
    structures; k-variable counting formulas reuse variables and have equality and relational \
    atoms and the counting quantifiers 'at least m'. Duplicator wins the n-round bijective \
    k-pebble game (Spoiler picks the pebble, then Duplicator the bijection) from a position \
    (S, a, b) iff a and b satisfy the same C^k formulas of quantifier rank at most n with free \
    variables in S; the infinite game corresponds to all C^k formulas. The easy direction holds \
    for arbitrary structures; the hard direction fails for infinite ones (N and R in the empty \
    language). Positions are total assignments, so for k > 0 the statements are vacuous on \
    empty structures. Cai, Furer and Immerman state the characterization on graphs, for the \
    equivalent game in which the players exchange sets of equal size."

register_result "immerman-lander" where
  title := "The Immerman–Lander theorem: color refinement characterizes two-variable counting \
    logic C²"
  topic := "descriptive complexity"
  sources := [
    { paper := ImmermanLander1990, theorem := unverified, locator := unverified },
    { paper := CaiFurerImmerman1992, theorem := "Theorem 5.2 (k = 1 case)",
      locator := "Section 5" },
    { paper := Immerman1999, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.bijPebbleWins_graph_empty_iff,
    Cslib.Logic.FO.bijPebbleWins_graph_singleton_iff,
    Cslib.Logic.FO.bijPebbleWins_graph_univ_iff,
    Cslib.Logic.FO.forall_realize_countingFormula_singleton_le_iff,
    Cslib.Logic.FO.forall_realize_countingFormula_singleton_iff,
    Cslib.Logic.FO.forall_realize_countingFormula_singleton_iff_card_add_card,
    Cslib.Logic.FO.forall_realize_countingFormula_empty_le_iff,
    Cslib.Logic.FO.forall_realize_countingFormula_empty_iff,
    Cslib.Logic.FO.forall_realize_countingFormula_empty_iff_card_add_card
  ]
  scope := "Finite LocallyFinite simple graphs over FirstOrder.Language.graph with the trivial \
    initial coloring fun _ => (). Round-by-round correspondence between Hella's bijective \
    2-pebble game (with 0, 1 or 2 placed pebbles) and color refinement: sentences of quantifier \
    rank at most n + 1 correspond to round-n color histograms (for nonempty vertex types, since \
    GenFormula.Realize takes a total assignment Fin 2 → V), and one-variable formulas of \
    rank at most n + 1 correspond to round-(n + 1) vertex colors paired with round-n histograms. \
    Full C²-equivalence reduces to round |V| + |W|. The k-dimensional generalization to C^(k+1) \
    is in weisfeiler-leman-counting; colored graphs with arbitrary initial colorings are not \
    formalized."

register_result "weisfeiler-leman-counting" where
  title := "Cai–Fürer–Immerman: k-dimensional Weisfeiler–Leman characterizes (k + 1)-variable \
    counting logic C^(k+1)"
  topic := "descriptive complexity"
  sources := [
    { paper := CaiFurerImmerman1992, theorem := "Theorem 5.2", locator := "Section 5" }
  ]
  theorems := [
    Cslib.Logic.FO.bijPebbleWins_graph_range_castSucc_iff,
    Cslib.Logic.FO.bijPebbleWinsForever_graph_range_castSucc_iff,
    Cslib.Logic.FO.bijPebbleWins_graph_empty_of_wlHistogram_eq,
    Cslib.Logic.FO.wlHistogram_eq_of_bijPebbleWins_graph_empty,
    Cslib.Logic.FO.bijPebbleWinsForever_graph_empty_iff_wlHistogram_eq,
    Cslib.Logic.FO.forall_realize_countingFormula_castSucc_le_iff,
    Cslib.Logic.FO.forall_realize_countingFormula_castSucc_iff,
    Cslib.Logic.FO.forall_realize_countingFormula_castSucc_iff_card_pow_add,
    Cslib.Logic.FO.realize_countingFormula_iff_of_wlHistogram_eq,
    Cslib.Logic.FO.wlHistogram_eq_of_forall_realize_countingFormula_empty_le,
    Cslib.Logic.FO.forall_realize_countingFormula_empty_iff_wlHistogram_eq,
    Cslib.Logic.FO.forall_realize_countingFormula_empty_iff_wlHistogram_card_pow_add,
    Cslib.Logic.FO.forall_wlColoring_one_eq_iff,
    Cslib.Logic.FO.forall_wlHistogram_one_eq_iff
  ]
  scope := "Uncolored finite simple graphs over FirstOrder.Language.graph with no LocallyFinite \
    or DecidableRel assumption, for every dimension k : ℕ. Folklore k-WL colors k-tuples from \
    their ordered atomic isomorphism type and refines by the multiset of (k + 1)-tuple step \
    profiles. Two k-tuples get the same round-n color iff they agree on C^(k+1) formulas of \
    quantifier rank at most n in the first k variables, and across all ranks iff they agree in \
    round |V|^k + |W|^k. For nonempty graphs, C^(k+1) sentence equivalence equals k-WL histogram \
    equality in all rounds and in round |V|^k + |W|^k, with a +k quantifier-rank shift for \
    individual rounds. The Cai–Fürer–Immerman lower-bound graphs separating C^(k+1) and k-WL \
    from isomorphism are in cai-furer-immerman-graphs; colored graphs are not formalized."

register_result "cai-furer-immerman-graphs" where
  title := "Cai–Fürer–Immerman lower-bound graphs separating C^(k+1) and k-WL from graph \
    isomorphism"
  topic := "descriptive complexity"
  sources := [
    { paper := CaiFurerImmerman1992, theorem := unverified, locator := "Section 6" }
  ]
  theorems := [
    Cslib.Logic.FO.bijPebbleWinsForever_cfiEven_cfiOdd,
    Cslib.Logic.FO.bijPebbleWins_cfiEven_cfiOdd,
    Cslib.Logic.FO.pebbleWinsForever_cfiEven_cfiOdd,
    Cslib.Logic.FO.realize_countingFormula_cfiEven_iff_cfiOdd,
    Cslib.Logic.FO.realize_formula_cfiEven_iff_cfiOdd,
    Cslib.Logic.FO.wlHistogram_cfiGraph_eq,
    Cslib.Logic.FO.wlHistogram_cfiEven_eq_cfiOdd_of_le,
    Cslib.Logic.FO.wlHistogram_cfiEven_eq_cfiOdd,
    Cslib.Logic.FO.colorHistogram_cfiEven_eq_cfiOdd,
    Cslib.Logic.FO.bijPebbleWinsForever_cfiGraph_empty,
    Cslib.Logic.FO.realize_countingFormula_cfiGraph_iff,
    Cslib.Logic.FO.exists_nonisomorphic_wlHistogram_eq
  ]
  scope := "Uncolored finite simple graphs over FirstOrder.Language.graph. For every k : ℕ, \
    cfiEven k and cfiOdd k are built over the complete base graph K_(2k+4) with parity gadgets \
    over ZMod 2 and triangle-apex uncoloring on each edge pair; their isomorphism \
    classification and non-isomorphism are in cai-furer-immerman-isomorphism. Duplicator wins \
    the infinite (k + 1)-pebble bijective game on cfiEven k and cfiOdd k, so they agree on all \
    C^(k+1) and FO^(k+1) sentences and have identical d-WL histograms in every round for all \
    d ≤ k. Using K_(2k+4) avoids degree-3 expanders at the cost of graphs of size exponential \
    in k rather than O(k); the linear-size expander lower bound is not formalized."

register_result "infinitary-fo-pebble-games" where
  title := "Pebble-game characterizations and expressiveness of L^k_∞ω and C^k_∞ω"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Theorem 11.5 and Proposition 11.8",
      locator := "Section 11.2, pp. 216–218" },
    { paper := KolaitisVardi1992, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.pebbleWins_iff_forall_infinitaryFormula_rankLE,
    Cslib.Logic.FO.pebbleWinsForever_iff_forall_infinitaryFormula,
    Cslib.Logic.FO.exists_isPebbleBackAndForth_iff_forall_infinitaryFormula,
    Cslib.Logic.FO.bijPebbleWins_iff_forall_infinitaryCountingFormula_rankLE,
    Cslib.Logic.FO.bijPebbleWinsForever_iff_forall_infinitaryCountingFormula,
    Cslib.Logic.FO.forall_realize_infinitaryFormula_iff_forall_realize,
    Cslib.Logic.FO.forall_realize_infinitaryCountingFormula_iff_forall_realize,
    Cslib.Logic.FO.FiniteVariable.realize_reachableInfinitary,
    Cslib.Logic.FO.FiniteVariable.realize_connectedInfinitary_iff_connected,
    Cslib.Logic.FO.FiniteVariable.realize_evenCardInfinitary,
    Cslib.Logic.FO.not_exists_infinitaryFormula_even_card
  ]
  scope := "k-variable infinitary logics L^k_∞ω (InfinitaryFormula) and C^k_∞ω \
    (InfinitaryCountingFormula) with arbitrary indexed disjunctions in Type w. For arbitrary \
    languages and arbitrary (possibly infinite) structures M : Type w₁, N : Type w₂, Duplicator \
    wins the n-round or infinite k-pebble game iff the positions satisfy the same L^k_∞ω \
    formulas of quantifier rank at most n (respectively all L^k_∞ω formulas) at index universe \
    max w₁ w₂; for finite structures, the bijective k-pebble game similarly characterizes \
    C^k_∞ω, and L^k_∞ω / C^k_∞ω equivalence over finite relational vocabularies collapses to \
    finitary FO^k / C^k equivalence. Expressiveness separations: graph reachability on all \
    simple graphs and connectivity on all nonempty simple graphs (Preconnected unconditionally) \
    are definable in L^3_∞ω, while EVEN is definable in C^1_∞ω on finite structures and not \
    definable in L^k_∞ω for any k."

register_result "even-linear-orders" where
  title := "EVEN is not first-order definable on finite linear orders"
  topic := "descriptive complexity"
  sources := [
    { paper := Kolaitis2007, theorem := unverified, locator := "Chapter 2" },
    { paper := Libkin2004, theorem := "Theorem 3.6 and Corollary 3.12",
      locator := "Chapter 3" }
  ]
  theorems := [
    Cslib.Logic.FO.FiniteLinearOrder.duplicatorWins_iff_card,
    Cslib.Logic.FO.FiniteLinearOrder.realize_iff_of_two_pow_le_card,
    Cslib.Logic.FO.FiniteLinearOrder.exists_sentence_of_card_ne,
    Cslib.Logic.FO.FiniteLinearOrder.not_exists_sentence_realize_iff_even
  ]
  scope := "Finite linear orders in Mathlib's language of orders (pure FO(≤); with BIT, EVEN \
    is definable). Duplicator wins the n-round game iff the orders have equal size or both \
    have at least 2^n - 1 elements, the sharp form in Kolaitis's survey; Libkin states the \
    sufficient condition with threshold 2^n. EVEN is not definable even above any size \
    threshold."

register_result "monadic-small-model" where
  title := "Löwenheim: the small model property for monadic sentences"
  topic := "descriptive complexity"
  sources := [
    { paper := Lowenheim1915, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Monadic.duplicatorWins_of_encard,
    Cslib.Logic.FO.Monadic.realize_iff_of_encard,
    Cslib.Logic.FO.Monadic.exists_substructure_realize,
    Cslib.Logic.FO.Monadic.exists_fin_realize
  ]
  scope := "Mathlib relational languages whose relation symbols have arity at most one, with \
    finitely many unary symbols; nullary symbols are allowed. A sentence of quantifier rank q \
    with a nonempty model has one on Fin (n + 1) with n + 1 ≤ max q 1 * 2 ^ k for k unary \
    symbols, through a substructure of the given model. The explicit bound and its proof by \
    Ehrenfeucht–Fraïssé games are proved here; Löwenheim is cited for the small model \
    property only. The resulting decision procedure and dichotomy for finite satisfiability \
    are in trakhtenbrot-dichotomy."

register_result "connectivity-not-fo" where
  title := "Connectivity is not first-order definable"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Corollary 3.19", locator := unverified },
    { paper := EbbinghausFlum1999, theorem := unverified, locator := "Chapter 2" }
  ]
  theorems := [
    Cslib.Logic.FO.Connectivity.not_exists_sentence_connected,
    Cslib.Logic.FO.Connectivity.not_exists_sentence_connected_of_le_card
  ]
  scope := "Finite simple graphs as structures of Mathlib's language of graphs, with no \
    built-in order or arithmetic, also when only graphs with at least t vertices are \
    considered. Proved by Ehrenfeucht–Fraïssé games through a reduction from EVEN on finite \
    linear orders."

register_result "bipartite-acyclic-not-fo" where
  title := "Bipartiteness and acyclicity are not first-order definable"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Exercises 3.4 and 3.5(3)", locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.GraphProperties.not_exists_sentence_isBipartite,
    Cslib.Logic.FO.GraphProperties.not_exists_sentence_isBipartite_of_le_card,
    Cslib.Logic.FO.GraphProperties.not_exists_sentence_isAcyclic,
    Cslib.Logic.FO.GraphProperties.not_exists_sentence_isAcyclic_of_le_card
  ]
  scope := "Mathlib's SimpleGraph.IsBipartite and SimpleGraph.IsAcyclic on finite simple graphs \
    in the pure language of graphs, also above any size threshold. Proved by adapting \
    Libkin's reduction from EVEN on finite linear orders (Corollary 3.19)."

register_result "hanf-gaifman-locality" where
  title := "Hanf and Gaifman locality of first-order logic"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Lemma 4.9, Theorem 4.12 and Corollary 4.13",
      locator := "Sections 4.2–4.3" }
  ]
  theorems := [
    Cslib.Logic.FO.Locality.HanfEquiv.duplicatorWins,
    Cslib.Logic.FO.Locality.HanfEquiv.realize_iff,
    Cslib.Logic.FO.Locality.realize_sentence_iff_of_nbhdIso,
    Cslib.Logic.FO.Locality.hanfEquiv_of_nbhdIso,
    Cslib.Logic.FO.Locality.NbhdIso.duplicatorWins,
    Cslib.Logic.FO.Locality.NbhdIso.realize_iff,
    Cslib.Logic.FO.Locality.NbhdIso.formula_realize_iff
  ]
  scope := "Finite structures. Hanf: equivalence at radius (3^n - 1)/2 gives Duplicator the \
    n-round game, so formulas of quantifier rank at most n agree; this form assumes M \
    nonempty. Gaifman: tuples with isomorphic radius-(3^(n+1) - 1)/2 neighborhoods agree on \
    such formulas. Game statements hold for every language, formula statements need a \
    relational one. Gaifman's normal form is not formalized."

register_result "locality-graph-properties" where
  title := "Being a tree is not first-order definable; locality bounds for graph properties"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Exercise 4.6",
      locator := "Section 4.1, Figure 4.2 (p. 48); Theorem 4.12 and the remark after \
        Corollary 4.13 (p. 52); Exercise 4.6 (p. 63)" }
  ]
  theorems := [
    Cslib.Logic.FO.Locality.not_exists_sentence_isTree,
    Cslib.Logic.FO.Locality.not_exists_sentence_isTree_of_le_card,
    Cslib.Logic.FO.Locality.card_le_of_realize_iff_connected,
    Cslib.Logic.FO.Locality.card_le_of_realize_iff_isTree,
    Cslib.Logic.FO.Locality.card_le_of_realize_iff_isAcyclic
  ]
  scope := "Finite simple graphs in the pure language of graphs, by Hanf locality. A sentence \
    of quantifier rank q holding exactly in the connected graphs on V forces \
    |V| ≤ 2·3^q + 1; for trees or acyclic graphs, |V| ≤ 2·3^q. The constants come from \
    Hanf's radius and are not claimed sharp. The module's sharper bounds for q ≥ 1 are \
    not registered."

register_result "transitive-closure-not-fo" where
  title := "Transitive closure and reachability are not first-order definable"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := unverified,
      locator := "Section 4.1, Figure 4.1 (p. 46); after Definition 4.7 (p. 49); \
        Section 4.3 (p. 54)" }
  ]
  theorems := [
    Cslib.Logic.FO.Locality.not_exists_formula_reflTransGen,
    Cslib.Logic.FO.Locality.not_exists_formula_transGen,
    Cslib.Logic.FO.Locality.not_exists_formula_reachable,
    Cslib.Logic.FO.Locality.card_le_of_realize_iff_reflTransGen,
    Cslib.Logic.FO.Locality.card_le_of_realize_iff_transGen,
    Cslib.Logic.FO.Locality.two_pow_le_of_gaifman_radius
  ]
  scope := "Finite structures of the pure language of graphs, by Gaifman locality. No formula \
    in two free variables defines the reflexive–transitive or transitive closure of the \
    edge relation, or reachability in finite simple graphs; on the successor relation of \
    Fin N, rank q forces N ≤ 2·3^(q+1). Any Gaifman radius on finite simple graphs for \
    rank n is at least 2^(n-1) (exact-locality-ranks gives the exact bound 2^n - 1 over \
    directed graphs with self-loops). Constants are not claimed sharp."

register_result "exact-locality-ranks" where
  title := "Exact Hanf (2^(n-1) - 1) and Gaifman (2^n - 1) locality ranks of first-order logic"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Exercises 4.10 and 4.11",
      locator := "Chapter 4 (pp. 63–64)" }
  ]
  theorems := [
    Cslib.Logic.FO.Locality.NbhdIso.duplicatorWins_of_equiv_two_pow,
    Cslib.Logic.FO.Locality.NbhdIso.duplicatorWins_of_two_pow,
    Cslib.Logic.FO.Locality.NbhdIso.realize_iff_of_two_pow,
    Cslib.Logic.FO.Locality.NbhdIso.formula_realize_iff_of_two_pow,
    Cslib.Logic.FO.Locality.HanfEquiv.duplicatorWins_of_two_pow,
    Cslib.Logic.FO.Locality.HanfEquiv.realize_iff_of_two_pow,
    Cslib.Logic.FO.Locality.HanfEquiv.formula_realize_iff_of_two_pow,
    Cslib.Logic.FO.Locality.realize_sentence_iff_of_nbhdIso_two_pow,
    Cslib.Logic.FO.Locality.exists_nbhdIso_realize_loopReach,
    Cslib.Logic.FO.Locality.two_pow_sub_one_le_of_gaifman_radius,
    Cslib.Logic.FO.Locality.exists_hanfEquiv_sentence_not_realize_iff,
    Cslib.Logic.FO.Locality.exists_hanfEquiv_formula_not_realize_iff,
    Cslib.Logic.FO.Locality.two_pow_pred_sub_one_le_of_hanf_sentence_radius,
    Cslib.Logic.FO.Locality.two_pow_pred_sub_one_le_of_hanf_radius
  ]
  scope := "Finite structures. Gaifman locality holds at radius 2^n - 1 and Hanf locality (for \
    nonempty M) holds at radius 2^(n-1) - 1, giving Duplicator the n-round game in any \
    language and formula/sentence agreement in relational languages. Matching lower bounds \
    over Mathlib's language of graphs (interpreted via relStructure as directed graphs with \
    self-loops) show that both radii are pointwise minimal across all quantifier ranks."

register_result "fo-tc-strict" where
  title := "FO(TC) is strictly more expressive than FO on finite structures"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := unverified,
      locator := "Definition 10.20 (p. 199); Section 4.1" }
  ]
  theorems := [
    Cslib.Logic.FO.TC.exists_formula_reflTransGen,
    Cslib.Logic.FO.TC.exists_formula_not_fo_equivalent
  ]
  scope := "Unordered finite structures of Mathlib's language of graphs, read as directed \
    graphs. One well-formed FO(TC) formula defines the reflexive–transitive closure of the \
    edge relation (the library's closure operator is reflexive), and no first-order \
    formula is equivalent to it on all finite structures."

register_result "color-refinement" where
  title := "Color refinement: stabilization, coarsest equitable partition and soundness"
  topic := "descriptive complexity"
  sources := [
    { paper := GroheKerstingMladenovSelman2014, theorem := unverified,
      locator := "Section 1 (Introduction), paragraph \"Colour Refinement on Matrices\"" }
  ]
  theorems := [
    SimpleGraph.ker_refinementColoring_eq,
    SimpleGraph.isEquitable_stableColoring,
    SimpleGraph.isGreatest_ker_stableColoring,
    SimpleGraph.not_exists_iso_of_colorHistogram_ne,
    SimpleGraph.isEmpty_iso_of_colorHistogram_ne,
    SimpleGraph.forall_refinementColoring_eq_iff,
    SimpleGraph.forall_colorHistogram_eq_iff,
    SimpleGraph.IsRegularOfDegree.colorHistogram_eq
  ]
  scope := "Finite LocallyFinite simple graphs with an arbitrary initial coloring χ₀ with k₀ \
    classes. The partition is stable from round |V| - k₀ and is the coarsest equitable \
    partition refining χ₀; the source states |V| + |W| rounds for a bipartite matrix from \
    the trivial partition. Differing histograms rule out color-preserving isomorphism; the \
    test is incomplete (equal-order d-regular graphs). The correspondence with \
    two-variable counting logic C² on uncolored simple graphs is in immerman-lander, and \
    folklore k-dimensional Weisfeiler–Leman is in weisfeiler-leman. Fractional isomorphism and a \
    certified algorithm are not formalized."

register_result "weisfeiler-leman" where
  title := "k-dimensional Weisfeiler–Leman: partition stabilization, soundness and two-graph \
    stabilization"
  topic := "descriptive complexity"
  sources := [
    { paper := CaiFurerImmerman1992, theorem := unverified, locator := "Section 5" }
  ]
  theorems := [
    SimpleGraph.ker_wlColoring_eq,
    SimpleGraph.ker_stableWLColoring,
    SimpleGraph.Iso.wlColoring_comp,
    SimpleGraph.Iso.wlHistogram_eq,
    SimpleGraph.isEmpty_iso_of_wlHistogram_ne,
    SimpleGraph.forall_wlColoring_eq_iff,
    SimpleGraph.forall_wlHistogram_eq_iff
  ]
  scope := "Uncolored finite simple graphs ([Fintype V], with no LocallyFinite or DecidableRel \
    assumption), for every dimension k : ℕ. Folklore k-WL colors Fin k → V by ordered atomic \
    isomorphism type at round 0 and by the multiset over all v : V of the atomic type of \
    Fin.snoc u v paired with the k single-coordinate replacement colors. The partition \
    stabilizes from round |V|^k - k₀ on, is isomorphism-invariant, and two-graph tuple or \
    histogram agreement in all rounds reduces to round |V|^k + |W|^k. The logical correspondence \
    with C^(k+1) is in weisfeiler-leman-counting, and the Cai–Fürer–Immerman lower-bound graphs \
    are in cai-furer-immerman-graphs and cai-furer-immerman-isomorphism; initial tuple \
    colorings and certified complexity bounds are not formalized."

register_result "cai-furer-immerman-isomorphism" where
  title := "Cai–Fürer–Immerman graphs over K_m: twist-parity isomorphism classification"
  topic := "descriptive complexity"
  sources := [
    { paper := CaiFurerImmerman1992, theorem := unverified, locator := "Section 6" }
  ]
  theorems := [
    SimpleGraph.isEmpty_iso_cfiGraph_of_sum_ne,
    SimpleGraph.not_nonempty_iso_cfiGraph_of_sum_ne,
    SimpleGraph.nonempty_iso_cfiGraph_iff_sum_eq,
    SimpleGraph.isEmpty_iso_cfiEven_cfiOdd,
    SimpleGraph.not_nonempty_iso_cfiEven_cfiOdd
  ]
  scope := "Uncolored finite simple Cai–Fürer–Immerman graphs cfiGraph m f over the complete \
    base graph K_m with twist f : Fin m → ZMod 2. Each edge pair is joined to an apex vertex so \
    that triangle membership separates edge and apex vertices from parity-gadget vertices \
    without vertex colors. Twisting f along an edge of K_m yields an isomorphic graph, and for \
    3 ≤ m two graphs cfiGraph m f and cfiGraph m g are isomorphic iff ∑ v, f v = ∑ v, g v; in \
    particular cfiEven k and cfiOdd k over K_(2k+4) are non-isomorphic. Indistinguishability \
    in C^(k+1) and k-WL is in cai-furer-immerman-graphs; expander base graphs of size O(k) are \
    not formalized."

register_result "native-sublinear-time-collapse" where
  title := "Sublinear native algorithms have constant runtime"
  topic := "time complexity"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Exercise 4.3",
      locator := "January 2007 draft r2.pdf, PDF p. 35; printed p. 151" }
  ]
  theorems := [
    Turing.MultiTapeTM.exists_uniform_time_of_fast_length,
    Turing.MultiTapeTM.exists_uniform_time_of_isLittleO,
    Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_const_time_of_isLittleO
  ]
  scope := "A fixed native sequential-input machine with a uniform sublinear clock on every \
    input word has a global constant clock. One fast width suffices under a uniform total \
    clock on all words. Raw-bit computability preserves outputs and independent workspace. \
    No separate input length, random access or arbitrary encoding extension is asserted."

register_result "sublinear-dtime-equals-constant" where
  title := "Sublinear deterministic time classes equal constant time"
  topic := "time complexity"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Exercise 4.3 (decision-class consequence)",
      locator := "January 2007 draft r2.pdf, PDF p. 35; printed p. 151" }
  ]
  theorems := [Cslib.Complexity.DTIME_eq_const_of_isLittleO]
  scope := "DTIME encBits p equals DTIME encBits 1 for p=o(n), including affine clock constants. \
    The input is every raw bit word; prefixes of arbitrary encoded instances need not be \
    valid, so no such encoding-general class identity is claimed."

register_result "goldreich-exact-step-counter" where
  title := "Exact native step counter from binary input"
  topic := "time complexity"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Exercise 4.5",
      locator := "January 2007 r2.pdf; PDF page 36 / printed page 152" },
    { paper := Goldreich2006DraftR1, theorem := "Numbers convention",
      locator := "December 2006 r1.pdf; PDF page 45 / printed page 20" }
  ]
  theorems := [Turing.MultiTapeTM.exists_stepCounter]
  scope := "One fixed finite deterministic native multitape machine on encNat n, \
    least-significant-first binary, visits one designated signal state exactly n times. \
    It starts outside the signal state and leaves each visit on the next transition. \
    Total runtime, including binary-to-unary preparation, is bounded by c*(n+1) for a \
    uniform constant c; zero input issues no signals. No logarithmic workspace or \
    per-prefix signal-latency bound is claimed."

register_result "translational-time-hierarchy" where
  title := "Deterministic time hierarchy below every power of the logarithm, by translation"
  topic := "time complexity"
  sources := [
    { paper := FortnowSanthanam2006,
      theorem := "Lemma 5 (the translation method only, not these statements)",
      locator := "Section 3.3" }
  ]
  theorems := [
    Cslib.Complexity.DTIME_pow_ssubset_DTIME_mul_iterSqrtLog_pow,
    Cslib.Complexity.DTIME_pow_ssubset_DTIME_of_pow_mul_log_rpow_le,
    Cslib.Complexity.DTIME_two_pow_ssubset_DTIME_two_pow_add_log_div,
    Cslib.Complexity.DTIME_two_pow_ssubset_DTIME_of_two_pow_mul_rpow_le
  ]
  scope := "DTIME(n^a) is strictly inside DTIME(g) whenever g(n) >= n^a (ln n)^eps eventually, \
    for every integer a >= 1 and real eps > 0, and DTIME(2^n) is strictly inside DTIME(g) \
    whenever g(n) >= 2^n n^eps eventually, on bit strings with native multitape DTIME. \
    Derived by translation (padding) from the library's polylogarithmic-gap diagonal theorem; \
    the source lemma is the translation method, not this statement. Only the bounds n^a and \
    2^n are covered, not arbitrary time-constructible t, and this is not W. J. Paul's \
    fixed-tape hierarchy."

register_result "liu-pass" where
  title := "Liu–Pass: one-way functions exist iff time-bounded Kolmogorov complexity is mildly \
    hard on average"
  topic := "meta-complexity"
  sources := [
    { paper := LiuPass2020, theorem := "Theorem 3.1",
      locator := "Section 3, p. 9 of arXiv:2009.11514v1" }
  ]
  theorems := [
    Cslib.Crypto.exists_oneWay_iff_exists_mildlyHardOnAverage_timeBoundedNat,
    Cslib.Crypto.exists_oneWay_iff_exists_mildlyHardOnAverageENat_timeBounded,
    Cslib.Crypto.exists_oneWay_iff_exists_forall_mildlyHardOnAverage_timeBoundedNat,
    Cslib.Crypto.exists_oneWay_iff_forall_exists_mildlyHardOnAverageToApprox_clog_timeBoundedNat,
    Cslib.Crypto.exists_oneWay_iff_forall_exists_mildlyHardOnAverageToApprox_timeBoundedNat
  ]
  scope := "Uniform one-way functions on bit strings and mild average-case hardness against \
    uniform strict PPT heuristics, for the library's multi-tape K^t. Item (b) takes a \
    polynomial clock p(n) >= n + 1 where the source writes t(n) > 0. Item (c) and the \
    threshold consequence are proved only in the polynomial-threshold form (some p, every \
    t >= p), with approximation windows d floor(log n) and d ceil(log n); the source's \
    near-linear range t(n) >= (1 + eps) n is not formalized."

register_result "kabanets-cai" where
  title := "Kabanets–Cai: if MCSP is in BPP, there are no one-way functions"
  topic := "meta-complexity"
  sources := [
    { paper := KabanetsCai2000, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Crypto.not_oneWay_of_MCSP_mem_BPP,
    Cslib.Crypto.not_oneWay_of_MCSP_mem_P,
    Cslib.Crypto.not_pseudorandomFunction_of_MCSP_mem_BPP
  ]
  scope := "Conditional. MCSP is the total truth-table language with De Morgan circuits \
    counting all gates, encoded as the table followed by the threshold in binary, and the \
    hypothesis is a bounded-error polynomial-time decider at all thresholds. Every keyed \
    family computable in polynomial time is then distinguished from a random function by a \
    uniform strict oracle PPT adversary with advantage at least 1/4, so no uniform one-way \
    function on bit strings exists."

register_result "formula-magnification" where
  title := "Oliveira–Santhanam: approximate-MCSP formula lower bounds above N polylog N give \
    NP ⊄ Formula[poly]"
  topic := "meta-complexity"
  sources := [
    { paper := OliveiraSanthanam2018, theorem := "Theorem 1(i) / Theorem 17(i) and Lemma 16",
      locator := "ECCC TR18-139, Section 1.2, p. 5; Section 3.1, pp. 14–15" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.not_NP_subset_FormulaPolyOn_of_approxMCSP_poly_hard,
    Cslib.Circuits.Boolean.not_NP_subset_FormulaPolyOn_of_approxMCSP_hard
  ]
  scope := "Conditional. De Morgan formulas measured by leaf size; approximate (1, 1 - 1/k)-MCSP \
    with s₁ <= s₂, integer k >= 1 and a non-strict agreement bound in the no-set. The \
    hypothesis is that for every c some 2^n-bit slice has no separating formula of leaf size \
    (2^n + 1) c (n + 1)^c (polynomially bounded s₂ and k), or the query-length analogue for \
    general parameters. The conclusion is that NP for the succinct MCSP encoding is not \
    contained in polynomial-size formulas."

register_result "formula-magnification-stretched" where
  title := "Oliveira–Santhanam: N^(1+ε) approximate-MCSP formula lower bounds give NP formula \
    lower bounds of size 2^(m^δ)"
  topic := "meta-complexity"
  sources := [
    { paper := OliveiraSanthanam2018, theorem := "Theorem 17(ii)",
      locator := "ECCC TR18-139, Section 3.1, p. 15" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.exists_NP_not_isBigO_formulaSize_of_approxMCSP_poly_hard,
    Cslib.Circuits.Boolean.exists_pos_not_isBigO_formulaSize_of_approxMCSP_hard
  ]
  scope := "Conditional. Polynomially bounded s₂ and k; the hypothesis is approximate-MCSP \
    formula leaf size above N^(1 + eps), N = 2^n, at arbitrarily large n. The conclusion gives \
    some delta > 0 such that a binary NP language (and every language agreeing with succinct \
    MCSP) has formula size not O(2^(m^delta))."

register_result "formula-magnification-subexp" where
  title := "Oliveira–Santhanam: approximate-MCSP formula lower bounds with subexponential \
    parameters give NP ⊄ Formula[poly]"
  topic := "meta-complexity"
  sources := [
    { paper := OliveiraSanthanam2018, theorem := "Theorem 17(iii)",
      locator := "ECCC TR18-139, Section 3.1, p. 15" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.not_NP_subset_FormulaPolyOn_of_approxMCSP_subexp_hard,
    Cslib.Circuits.Boolean.not_NP_subset_FormulaPolyOn_of_approxMCSP_rpow_hard
  ]
  scope := "Conditional. Subexponentially bounded s₂ and k; the hypothesis is approximate-MCSP \
    formula leaf size above 2^(n + n/d) for a fixed d > 0, or above N^(1 + eps), at \
    arbitrarily large n. The conclusion is that NP for the succinct MCSP encoding is not \
    contained in polynomial-size formulas."

register_result "formula-magnification-average-case" where
  title := "Oliveira–Santhanam: one-sided zero-error average-case formula lower bounds for MCSP \
    give NP ⊄ Formula[poly]"
  topic := "meta-complexity"
  sources := [
    { paper := OliveiraSanthanam2018, theorem := "Theorem 27",
      locator := "ECCC TR18-139, Section 3.3, p. 21" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.exists_NP_not_mem_FormulaPoly_of_zero_error_average_case_subexp_hard,
    Cslib.Circuits.Boolean.not_mem_FormulaPoly_of_zero_error_average_case_subexp_hard
  ]
  scope := "Conditional, for De Morgan formulas only. Subexponentially bounded s; average-case \
    solvers are one-sided formulas accepting every yes-instance of MCSP[s] and at most \
    2^(2^n - n) truth tables, with the lower bound 2^(n/d) for fixed d > 0 at arbitrarily \
    large n. The conclusion is a binary NP language without polynomial-size formulas, weaker \
    than the source's 2^Omega(n)."

register_result "formula-magnification-ternary" where
  title := "Oliveira–Santhanam: sublinear zero-error average-case formula lower bounds for \
    MCSP[2^√n] imply NP ⊄ Formula[poly]"
  topic := "meta-complexity"
  sources := [
    { paper := OliveiraSanthanam2018, theorem := "Theorem 5",
      locator := "ECCC TR18-139, Section 1.2, p. 8; Appendix A, Definition 43, p. 34" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.exists_NP_not_mem_FormulaPoly_of_sqrtThreshold_average_case_hard,
    Cslib.Circuits.Boolean.exists_NP_not_mem_FormulaPoly_of_sqrtThreshold_half_average_case_hard,
    Cslib.Circuits.Boolean.exists_NP_not_mem_FormulaPoly_of_zero_error_average_case_sublinear_hard
  ]
  scope := "If no nonuniform family of ternary De Morgan formula devices (an unknown mask and an \
    answer formula) with o(2^n) total leaves solves MCSP[⌊2^√n⌋] on 2^n-bit truth tables with \
    zero error, answering ? on at most a 1/n fraction of truth tables for every large n \
    (Definition 43), then some binary NP language has no polynomial-size De Morgan formulas; \
    the general form takes any subexponential threshold. Circuit size counts every De Morgan \
    gate. Conditional: no formula lower bound for MCSP is proved."

register_result "formula-magnification-locality" where
  title := "Chen–Hirahara–Oliveira–Pich–Rajgopal–Santhanam: the Oliveira–Santhanam formula \
    magnification reduction is local"
  topic := "meta-complexity"
  sources := [
    { paper := ChenHiraharaOliveiraPichRajgopalSanthanam2020,
      theorem := "Proposition 63, [OS18] MCSP bullet",
      locator := "ECCC TR19-168, Appendix A.2, p. 52; Section 2.5, Definition 11, p. 13" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.exists_oracleFormula_separating_approxMCSP,
    Cslib.Circuits.Boolean.localFormulaClass_approxMCSP,
    Cslib.Circuits.Boolean.localFormulaClass_approxMCSP_real_poly
  ]
  scope := "MCSP[(s, 0), (s, δ)] on N = 2^n-bit truth tables is computed by De Morgan formulas \
    with at most N oracle gates, each of fan-in at most 98·(⌈1/δ⌉·(s + 1))^3, adaptivity 1 and \
    N times that many input leaves, under one fixed oracle (encoded SuccinctMCSP) for all \
    lengths, when n ≤ s(n) and 0 < δ(n). Formulas only: for the [q, ℓ, a]-Circuit classes \
    (LocalCircuitClass) the Gap-MCSP [OPS19] bullet is registered as gap-mcsp-oracle-circuits \
    and the MCSP [MMW19] bullet as mmw-merge-tree-locality; the other bullets of Proposition 63 \
    and the locality barrier (Theorem 59) are not formalized."

register_result "mmw-merge-tree-locality" where
  title := "Chen–Hirahara–Oliveira–Pich–Rajgopal–Santhanam: the McKay–Murray–Williams merge tree \
    puts MCSP[s] in [O(N/s), O(s⁴), O(n/log s)]-Circuit[O(N/s)] for n ≤ s ≤ N"
  topic := "meta-complexity"
  sources := [
    { paper := ChenHiraharaOliveiraPichRajgopalSanthanam2020,
      theorem := "Proposition 63, [MMW19] MCSP bullet",
      locator := "ECCC TR19-168, Appendix A.2, p. 52; Section 2.5, Definition 11, p. 13" }
  ]
  theorems := [
    Cslib.MCSP.localCircuitClass_MCSP
  ]
  scope := "Unconditional. Whenever n ≤ s(n) and 2 ≤ s(n) for every n, MCSP[s] (no gap) is in \
    LocalCircuitClass (Definition 11) at input length m, with n = log₂ m: at most 128m/s(n) + 1 \
    oracle gates, each of fan-in at most 12·s(n)^4, at most n/⌊log₂ s(n)⌋ + 1 oracle gates on any \
    path, and at most 129m/s(n) + 3 gates (all gates counted). The circuits are the explicit \
    merge tree MergeTree.mmwCircuit, with ⌊log₂ s⌋ bits per level, under one fixed oracle, \
    MergeTree.oracle, for all lengths; no bound on the oracle's complexity is claimed. The bounds \
    read as the source's O(N/s) and O(n/log s) when also s(n) ≤ 2^n. Deviations: the source \
    assumes only a constructive s(n) ≤ 2^n/poly(n); n ≤ s(n) and 2 ≤ s(n) exclude s(n) < n, the \
    exact bounds need no upper bound on s, and constructivity is not formalized (the class is \
    nonuniform)."

register_result "murray-williams" where
  title := "Murray–Williams: if MCSP is NP-hard, then EXP ≠ NP ∩ P/poly and EXP ≠ ZPP"
  topic := "meta-complexity"
  sources := [
    { paper := MurrayWilliams2017, theorem := "Theorems 1.6 and 4.1",
      locator := "Section 1, p. 5; Section 4.1, p. 13" }
  ]
  theorems := [
    Cslib.Complexity.EXP_eq_NEXP_of_MCSP_npHard_of_EXP_subset_PPoly,
    Cslib.Complexity.not_EXP_subset_NP_inter_PPolyOn_of_MCSP_npHard,
    Cslib.Complexity.EXP_ne_NP_inter_PPolyOn_of_MCSP_npHard,
    Cslib.Complexity.EXP_ne_ZPP_of_MCSP_npHard
  ]
  scope := "Conditional. The hypothesis is NP-hardness of the total truth-table MCSP (binary \
    threshold, all gates counted) under polynomial-time many-one reductions; Theorem 4.1 \
    assumes only reductions from sparse NP languages, so the formalization is its full-NP-hard \
    specialization. Classes are over bit strings with native multi-tape machines; \
    EXP ≠ NP ∩ P/poly uses the library's nondeterministic time hierarchy."

register_result "anti-checker" where
  title := "Small anti-checkers for functions without small circuits"
  topic := "meta-complexity"
  sources := [
    { paper := LiptonYoung1994, theorem := unverified, locator := unverified },
    { paper := OliveiraPichSanthanam2019, theorem := "Lemma 4.7 (ordered-tuple variant)",
      locator := "Section 4" }
  ]
  theorems := [
    Cslib.MCSP.exists_isAntiChecker,
    Cslib.MCSP.exists_lt_complexityOn,
    Cslib.MCSP.exists_ofFunction_notMem
  ]
  scope := "Unconditional, nonuniform existence. For m > 0, if no m members of a family of \
    fewer than 2^b functions on at most 2^m inputs have f as strict majority, some set of at \
    most 16 b inputs refutes every member. For circuits with n <= m: if f needs more than m s \
    gates plus those of strict majority on m bits, f needs more than s gates on some set of at \
    most 16 b inputs. Ordered tuples give the share 1/16 \
    where the source gets 1/(2m). The efficient anti-checker lemma under NP ⊆ P/poly \
    (Oliveira–Pich–Santhanam Lemma 4.1) is registered as efficient-anti-checker."

register_result "efficient-anti-checker" where
  title := "Oliveira–Pich–Santhanam: under NP ⊆ P/poly, anti-checkers are generated by circuits of \
    size 2^(n + O(βn))"
  topic := "meta-complexity"
  sources := [
    { paper := OliveiraPichSanthanam2019, theorem := "Lemma 4.1 (ECCC TR18-158 Lemma 17)",
      locator := "ECCC TR18-158, Section 4.1, p. 16" }
  ]
  theorems := [
    Cslib.MCSP.AntiChecker.exists_antiChecker_circuit_of_NP_subset_PPoly,
    Cslib.MCSP.AntiChecker.exists_antiChecker_circuit_le_of_NP_subset_PPoly
  ]
  scope := "Conditional on NP ⊆ P/poly (NP encBits ⊆ PPolyOn encBits). There is k such that for \
    every β > 0 and all large n, a De Morgan circuit with at most 2^(n + kβn) gates (all gates \
    counted) maps the truth table of f : {0,1}^n → {0,1} to ⌊2^(10βn)⌋₊ blocks of n bits, and if \
    ⌊2^(βn)⌋₊ < complexity f, every circuit with at most ⌊2^(βn)/(10n)⌋₊ gates errs on some \
    block. Every β > 0, where the source says sufficiently small β. The explicit form bounds the \
    size by 2^n·c·(n + s + 1)^c for every n > 0, s and enough blocks, assuming f needs more gates \
    than n circuits with s gates and their strict majority. Proof route: a deterministic greedy \
    against a hash-threshold oracle with tensor-power amplification, compiled to an oracle \
    circuit whose oracle gates are replaced by P/poly circuits; not the source's approximate \
    counting and listing."

register_result "gap-mcsp-oracle-circuits" where
  title := "Chen–Hirahara–Oliveira–Pich–Rajgopal–Santhanam: Gap-MCSP has oracle circuits with \
    N·poly(s) gates, fan-in poly(s) and adaptivity poly(s)"
  topic := "meta-complexity"
  sources := [
    { paper := ChenHiraharaOliveiraPichRajgopalSanthanam2020,
      theorem := "Proposition 63, [OPS19] Gap-MCSP bullet",
      locator := "ECCC TR19-168, Appendix A.2, p. 52; Section 2.5, Definition 11, p. 13" }
  ]
  theorems := [
    Cslib.MCSP.exists_oracleCircuit_gapMCSP,
    Cslib.MCSP.localCircuitClass_gapMCSP
  ]
  scope := "Unconditional. Whenever n·s₁ + 2 + 2n(n + 2) ≤ s₂ at length n, one oracle circuit on \
    N = 2^n inputs with the fixed oracle antiCheckerOracle accepts the yes-instances of \
    Gap-MCSP[s₁, s₂] and rejects its no-instances. It has at most 5000·N·s₂^5 gates, at most \
    610·N·s₂^4 + 1 oracle gates, fan-in at most 5000·s₂^5 and at most 610·s₂^4 + 1 oracle gates \
    on any path. localCircuitClass_gapMCSP states this in the class LocalCircuitClass \
    (Definition 11) at input length m with n = log₂ m, the gap condition holding at every n; its \
    size bound has a + 1 for input length 0, which has no instances. The gap condition replaces \
    the source's constructive s(n) ≤ 2^n/poly(n)."

register_result "arora-barak-uniform-restriction-largeness" where
  title := "Random Boolean functions remain nonconstant on all large subcubes"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 22, Exercise §2",
      locator := "2007-01-08 public draft, printed p. 443 / PDF p. 459" }
  ]
  theorems := [Cslib.Circuits.Boolean.tendsto_prob_no_constant_restriction]
  scope := "For each fixed real ε in (0, 1), the probability tends to one as the input length n \
    grows. The truth table is uniform over all Boolean functions on n bits. Every partial \
    assignment fixing at most n − n^ε coordinates must leave a nonconstant function. The real \
    cutoff is equivalent to requiring at least ⌈n^ε⌉ free coordinates. This is the largeness \
    claim for Example 22.5."

register_result "natural-proofs" where
  title := "Razborov–Rudich: subexponentially secure generators rule out natural proofs \
    against P/poly"
  topic := "meta-complexity"
  sources := [
    { paper := RazborovRudich1997, theorem := unverified, locator := "Section 4" },
    { paper := GGM1986, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Boolean.not_isUseful_PPoly_of_isNatural_of_generator
  ]
  scope := "Conditional. If a family of length-doubling generators with polynomial circuit \
    complexity is subexponentially secure against circuits (for long seeds of length k, \
    tests with at most 2^m gates, m^d <= k, have advantage at most 2^-m), then no \
    P/poly-natural property is useful against P/poly. The generator tests are nonuniform \
    circuits reading the 2k-bit outputs; the barrier's derived tests read whole truth tables \
    of the GGM keyed family. The generator family is a hypothesis, not a constructed object."

register_result "learning-hardness-from-generators" where
  title := "Subexponentially secure generators rule out learners with small circuits for \
    polynomial-size circuits"
  topic := "meta-complexity"
  sources := [
    { paper := Valiant1984, theorem := unverified, locator := unverified },
    { paper := GGM1986, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.UniformLearning.eventually_le_of_isSubexponentiallySecure,
    Cslib.MachineLearning.UniformLearning.exists_eventually_not_learns_of_isSubexponentiallySecure
  ]
  scope := "Conditional on a subexponentially secure family of length-doubling generators of \
    polynomial circuit complexity, as in natural-proofs. For a polynomial s, every c and large n, \
    a learner whose tests are circuits of at most 2^(cn) gates on truth tables (HasCircuitTests) \
    for the functions of circuit size s n has (1 - delta)(1 - eps) <= 1/2 + q/2^(n+1) + 2^(-cn). \
    Learners with q <= 2^(n-1) adaptive membership queries and De Morgan circuits of S <= 2^(cn) \
    gates in all on each seed (HasAdaptiveCircuit, covering non-adaptive HasCircuit learners) \
    have such tests, so none reaches (1 - delta)(1 - eps) > 3/4. Running time is not modelled. \
    The distinguisher fixes the learner's seed and comparison point by averaging; it is a \
    nonuniform circuit test."

register_result "learning-natural-property" where
  title := "Oliveira–Santhanam: learners for SIZE s yield P/poly-natural properties useful against \
    SIZE s"
  topic := "meta-complexity"
  sources := [
    { paper := OliveiraSanthanam2017, theorem := "Theorem 8, (1) ⇒ (5)", locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.UniformLearning.isNatural_PPoly_and_isUseful_SIZE,
    Cslib.MachineLearning.UniformLearning.isNatural_PPoly_lowAgreement,
    Cslib.MachineLearning.UniformLearning.isUseful_lowAgreement
  ]
  scope := "Membership-query learners (adaptive allowed) with uniform seeds from a set of size \
    2^(c(n+1)), circuit tests of at most 2^(c(n+1)) gates on truth tables (HasCircuitTests), and \
    accuracy \
    (1 - delta)(1 - eps) at least 2^(-cn) above 1/2 + q/2^(n+1). The property is the set of \
    functions on which the seed-averaged agreement is below (1 - delta)(1 - eps); it is decided \
    by an exact threshold over all seeds and points, so constructivity is P/poly by circuit size, \
    not the source's BPP-natural form, and arbitrary seed distributions are not covered. The \
    random-function bound is the fair-coin argument, not the source's small-hypothesis lemma. \
    The accuracy gap restricts it to strong or confidence-amplified learners; the source's \
    non-trivial (1/2 - 1/n^k, 1/n) learners of item (1) are not covered as stated."

register_result "nw-reconstruction-learner" where
  title := "Carmosino–Impagliazzo–Kabanets–Kolokolova: the Nisan–Wigderson reconstruction as a \
    membership-query weak learner, one run"
  topic := "meta-complexity"
  sources := [
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016, theorem := "Theorem 2.11",
      locator := "Section 2.4" },
    { paper := NisanWigderson1994, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.UniformLearning.nwLearner_learns_of_dens,
    Cslib.MachineLearning.UniformLearning.nwLearner_learns,
    Cslib.MachineLearning.UniformLearning.div_two_mul_le_dens_uniformError_nwLearner_le,
    Cslib.MachineLearning.UniformLearning.nwLearner_queriesAtMost,
    Cslib.MachineLearning.UniformLearning.complexity_eval_nwLearner_le
  ]
  scope := "One run of the reconstruction, in a library form. For an (l, n, a)-design with m > 0 \
    blocks and a deterministic test accepting at least a delta fraction of m-bit strings but \
    no output of the generator of any f in the class, the learner built from the negated test \
    learns the class under the uniform distribution with membership queries, error \
    1/2 - delta/(2m) and success probability delta/(2m) over a uniform trial. This is the \
    delta-dense natural-property case; nwLearner_learns covers a distinguisher of any \
    advantage eps, where the source takes advantage above 1/5, and advantage eps/(2m) \
    replaces 1/L (the source's L is the output length m). It makes at most \
    m 2^a queries, and every hypothesis has De Morgan circuit size at most that of the test \
    plus m (2^a (2a + 3) + 1) + 1. The running time of the learner is not certified. Repeating \
    runs and selecting the best hypothesis, which the full Theorem 2.11 needs, is the entry \
    nw-reconstruction-best-of."

register_result "nw-reconstruction-best-of" where
  title := "Carmosino–Impagliazzo–Kabanets–Kolokolova: learning from a distinguisher for the \
    Nisan–Wigderson generator"
  topic := "meta-complexity"
  sources := [
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016, theorem := "Theorem 2.11",
      locator := "p. 10:9" }
  ]
  theorems := [
    Cslib.MachineLearning.UniformLearning.bestOf_nwLearner_learns,
    Cslib.MachineLearning.UniformLearning.bestOf_nwLearner_learns_of_dens,
    Cslib.MachineLearning.UniformLearning.bestOf_nwLearner_queriesAtMost,
    Cslib.MachineLearning.UniformLearning.complexity_eval_bestOf_nwLearner_le
  ]
  scope := "Theorem 2.11 in a library form. For an (l, n, a)-design with m > 0 blocks and a \
    deterministic test that accepts outputs of the generator of each f in the class with \
    probability at least eps > 0 more than uniform m-bit strings, best-of-k selection on t \
    uniform sample points over the reconstruction learner built from the test learns the class \
    under the uniform distribution with membership queries, error 1/2 - eps/(4m) and confidence \
    1 - eta, when eps/(2m) <= 1, log(2/eta) <= (eps/(2m)) k and 8 log(4k/eta) <= t (eps/(2m))^2. \
    Any advantage eps > 0 replaces the source's advantage above 1/5, error 1/2 - eps/(4m) \
    replaces 1/2 - 1/L (the source's L is the output length m), and explicit k and t replace \
    poly(L). bestOf_nwLearner_learns_of_dens is the natural-property special case: a test \
    accepting at least a delta > 0 fraction of m-bit strings but no generator output, used \
    through its negation, which has advantage at least delta. It makes at most k m 2^a + t \
    queries, and every hypothesis has the De Morgan circuit bound of one run. The running time \
    of the learner is not certified."

register_result "cikk-amp-reconstruction" where
  title := "Carmosino–Impagliazzo–Kabanets–Kolokolova: learning f from a learner for its \
    amplification (f^k)^GL"
  topic := "meta-complexity"
  sources := [
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016,
      theorem := "Theorem 4.3, with Claim 4.4 in its proof",
      locator := "pp. 10:15–10:16; Claim 4.4 stated on p. 10:15" },
    { paper := ImpagliazzoJaiswalKabanetsWigderson2010, theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.UniformLearning.learns_ampLearner,
    Cslib.MachineLearning.UniformLearning.queriesAtMost_ampLearner,
    Cslib.MachineLearning.UniformLearning.eval_ampLearner
  ]
  scope := "The reconstruction for p = 2 in a library form, with the GF(2) amplification \
    Amp(f) = (f^k)^GL. If a membership-query learner learns {Amp(f) | f in C} under the uniform \
    distribution with error 1/2 - gamma and success probability p, then the black-box reduction \
    that answers each of its queries with k queries to f, decodes its hypothesis with \
    Goldreich-Levin and then with the direct-product decoder learns C with error eps and \
    success probability p delta0^2/8, where delta0 = gamma/2^(K+3), when \
    k <= 2 (gamma/2)^2 (2^K - 1), 2s <= k, s >= (64/eps) log(512/(eps delta0^2)) and \
    m >= (16/delta0) log(8/eps). Claim 4.4, the Goldreich-Levin step, is \
    dens_filter_glAmpCandidate_agree in HardnessAmplification/GLAmpDecode.lean, used in the \
    proof. Deviations: (a) the Goldreich-Levin list has 2^K = O(k/gamma^2) \
    entries, where the source's Goldreich-Rubinfeld-Sudan decoder has O(1/gamma^2); (b) each \
    seed gives a deterministic decoder, and a delta0 fraction of the seeds has agreement at \
    least delta0, by reverse Markov; (c) the success probability and the direct-product \
    constants are ours, and p delta0^2/8 >= p gamma^6/(10368 k^2) for the least admissible K; \
    (d) the four parameter conditions are hypotheses, where the source fixes \
    k = ceil(3c (1/eps) ln(1/gamma)) + 1. The size s of the direct-product set is an explicit \
    argument, and the seed distribution needs k > 0 and s <= k. The circuit size of the \
    hypotheses is not bounded here (see cikk-learner-hypothesis-size), and the running time of \
    the learner is not certified."

register_result "cikk-learning-from-dense-test" where
  title := "Carmosino–Impagliazzo–Kabanets–Kolokolova: learning f from a dense test that rejects \
    the generator of its amplification, p = 2"
  topic := "meta-complexity"
  sources := [
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016,
      theorem := "Theorem 5.1, with the composition from the proof of Theorem 3.2",
      locator := "p. 10:19; proof of Theorem 3.2 on p. 10:11" }
  ]
  theorems := [
    Cslib.MachineLearning.UniformLearning.learns_cikkLearner,
    Cslib.MachineLearning.UniformLearning.queriesAtMost_cikkLearner,
    Cslib.MachineLearning.UniformLearning.queriesAtMost_cikkLearner_two_pow
  ]
  scope := "The learner of Theorem 5.1 for p = 2 in a per-function black-box form. Let a test on \
    2^l-bit strings accept at least 2^(2^l) 2^(l+1-g) strings and no output of the \
    Nisan-Wigderson generator of Amp(f) = (f^k)^GL, k = cikkK e g, on the binary polynomial \
    design, for every f in C. Then cikkLearner, best-of selection over the amplification \
    reconstruction (cikk-amp-reconstruction) of the Nisan-Wigderson learner of the negated test \
    (nw-reconstruction-learner), learns C under the uniform distribution with membership \
    queries, error 2^-e and confidence 1 - 2^-h, with at most \
    (h+1) 2^(2l + 10g + 6e + 59) queries. Labelled deviations: (1) a single outer best-of \
    selection replaces the source's per-stage confidence boosts (proof of Theorem 3.2), with \
    the same result up to constants; (2) any density at least 2^(l+1-g) replaces largeness \
    1/5, and the Nisan-Wigderson advantage is delta/(2L) instead of 1/L; (3) error, \
    confidence and k are powers of two with this library's constants, where the source has \
    k = ceil(3c (1/eps) ln(1/gamma)) + 1, and the deviations of cikk-amp-reconstruction carry \
    over; (4) the number of queries is certified, the hypothesis size is bounded in \
    cikk-learner-hypothesis-size, and the running time is not certified; (5) p = 2 only; \
    (6) the test is an arbitrary Boolean function, not a natural property, so the \
    property-to-learner form of Theorem 5.1 is not included; Corollary 5.4 for p = 2 is \
    cikk-learning-ac0-2."

register_result "cikk-learner-hypothesis-size" where
  title := "Carmosino–Impagliazzo–Kabanets–Kolokolova: the hypotheses of the learner from a \
    dense test are small circuits relative to the test, p = 2"
  topic := "meta-complexity"
  sources := [
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016,
      theorem := "Theorem 5.1, the size of the hypothesis circuit", locator := "p. 10:19" }
  ]
  theorems := [
    Cslib.MachineLearning.UniformLearning.complexity_eval_cikkLearner_le,
    Cslib.MachineLearning.UniformLearning.complexity_eval_cikkLearner_le_two_pow,
    Cslib.MachineLearning.UniformLearning.complexity_eval_ampLearner_le
  ]
  scope := "On every target and seed, the hypothesis of the learner of \
    cikk-learning-from-dense-test has De Morgan circuit size at most \
    T (F+1) ((2^K - 1)(c + N + 3) + 8 + 2 (2^K - 1)(2^K + 1)) + 3T + 1, where c is the circuit \
    size of the test, N = 2^l (2^(l-1) (2(l-1) + 3) + 1), and T, F, K are the numbers of \
    trials, fixed positions and masks; in closed form, at most 2^(11g + 9e + 3l + 80) (c + 1). \
    The bound composes the Nisan-Wigderson hypothesis bound (nw-reconstruction-learner), the \
    Goldreich-Levin candidate bound and the direct-product decoder bound \
    (complexity_dpDecode_le); complexity_eval_ampLearner_le is the step for one run of the \
    amplification reconstruction (cikk-amp-reconstruction). The bound is affine in c with \
    T (F+1)(2^K - 1) copies of the test. Labelled deviations: (1) with unit-cost test gates \
    it is the size that the source's oracle circuit would have, but that oracle circuit is not \
    built; (2) the constants, including the closed form's, are this library's and not tight; \
    (3) size only: depth and the running time of the learner are not certified."

register_result "cikk-learning-ac0-2" where
  title := "Carmosino–Impagliazzo–Kabanets–Kolokolova: learning AC⁰[2] with the rank property, \
    with quasi-polynomially many membership queries and quasi-polynomial-size hypotheses"
  topic := "meta-complexity"
  sources := [
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016,
      theorem := "Theorem 5.1 and Corollary 5.4, p = 2",
      locator := "p. 10:19 (Theorem 5.1 and its proof); p. 10:20 (Corollary 5.4)" }
  ]
  theorems := [
    Cslib.MachineLearning.UniformLearning.learns_cikkLearner_rankTest,
    Cslib.MachineLearning.UniformLearning.queriesAtMost_cikkLearner_rankTest,
    Cslib.MachineLearning.UniformLearning.queriesAtMost_cikkLearner_rankTest_le,
    Cslib.MachineLearning.UniformLearning.complexity_eval_cikkLearner_rankTest_le_two_pow,
    Cslib.MachineLearning.UniformLearning.complexity_eval_cikkLearner_rankTest_le
  ]
  scope := "Corollary 5.4 for p = 2 with queries and hypothesis size counted, for a fixed depth d \
    and size s. With g = cikkAC0Gap d e n s and l = cikkAC0Len d e n s g, the CIKK learner \
    (cikk-learning-from-dense-test) whose test accepts the truth tables of the rank property \
    (rank-property-natural-ac0-2) at input length l learns every function on n bits computed \
    by a circuit of NOT, unbounded fan-in AND/OR and MOD_2 gates of depth at most d and size at \
    most s, under the uniform distribution with membership queries, with error 2^-e and \
    confidence 1 - 2^-h. It makes at most (h+1) 2^(12g + 6e + 59) queries, and \
    g <= 2^(2D(5D+25)) B^(2D) with D = d + 7 and B = floor(log2(M^2 (s + 6(n+1)^2 + 3))) + 1, \
    M = 2^(e+10)(3e+42), so for fixed d the number of queries is quasi-polynomial in n, s and \
    2^e. On every target and seed the hypothesis has a De Morgan circuit with at most \
    2^(17g + 9e + 76) gates, also quasi-polynomial for fixed d: the rank test's truth-table \
    circuit (173 * 8^l gates) fed into cikk-learner-hypothesis-size, with l + 2 <= g. Labels: \
    (1) the rank property is this library's variant (one square matrix, threshold C(n, a)/2, \
    level sliceLevel) with density 1/2 where Theorem 5.1 assumes largeness 1/5, and its \
    constructivity is used only as truth-table circuit size, not the source's NC^2; (2) p = 2 \
    only, where Corollary 5.4 states every prime; (3) queries and De Morgan hypothesis size are \
    certified, but the source's running-time bound is not; hypothesis depth is not certified, \
    so the hypotheses are not shown to lie in AC^0[2] (Corollary 5.4's hypotheses are general \
    circuits too); (4) the target class is nonuniform, fixed by d and s; (5) g and \
    l are explicit closed forms from the fixed point l + 2 <= g, replacing the source's choice \
    of L with log L > u^-1(poly); the generator circuits add depth 7, and all constants are \
    this library's; (6) the deviations of cikk-learning-from-dense-test carry over. The \
    abstract form of Theorem 5.1, from any natural property useful against a class, is not \
    included."

register_result "chaitin-incompleteness" where
  title := "Chaitin's incompleteness theorem for plain Kolmogorov complexity"
  topic := "Kolmogorov complexity"
  sources := [
    { paper := Chaitin1974, theorem := unverified, locator := unverified },
    { paper := LiVitanyi2019, theorem := unverified, locator := "Chapter 2" }
  ]
  theorems := [
    Cslib.Kolmogorov.DescriptionMethod.MinorizesPartrec.exists_forall_le_complexity_universal_add,
    Cslib.Kolmogorov.DescriptionMethod.MinorizesPartrec.exists_forall_le_of_rePred_of_read,
    Cslib.Kolmogorov.DescriptionMethod.MinorizesPartrec.exists_notMem_of_rePred
  ]
  scope := "Plain complexity under any description method of a Primcodable type that is at most \
    an additive constant worse than every partial recursive decoder. Formal systems are r.e. \
    predicates on Primcodable sentences with a computable reading of n <= C(x), and soundness \
    is a hypothesis. The quantitative bound is C(encode e) + c for a code e semi-deciding the \
    collection. Prefix-free complexity, Chaitin's Omega and logic-level theories are not \
    formalized."

register_result "goldreich-kolmogorov-universal" where
  title := "Kolmogorov complexity with respect to a universal machine"
  topic := "Kolmogorov complexity"
  sources := [
    { paper := Goldreich2006DraftR1, theorem := "Theorem 1.10",
      locator := "December 2006 r1.pdf, printed p. 34; PDF p. 59" }
  ]
  theorems := [Turing.MultiTapeTM.IsUniversal.exists_ecomplexity_le]
  scope := "The compared machine M is a deterministic native multi-tape machine over Bool with \
    finitely many states, run on arbitrary bit strings. The universal machine U is any \
    deterministic native multi-tape machine over Bool, with any state type, satisfying \
    IsUniversal (Definition 1.8): on encPair encBits encBits (eDesc (desc eS eBit M'), x) it \
    halts with output o exactly when M' halts on x with o, for every finite-state binary M'; \
    the finite-state case includes the source's machines. The pair encoding writes each \
    description bit b as 1b, then 0, so the constant is 2|<M>| + 1. Complexities are extended \
    naturals, top without a description. Universality is a hypothesis: an unclocked native \
    universal machine (Theorem 1.9) is not constructed. Outside-fleet source check: \
    https://github.com/cslib-community/cslib-frontier/pull/6289#pullrequestreview-5947845222"

register_result "symmetry-of-information" where
  title := "Kolmogorov–Levin symmetry of information for plain complexity"
  topic := "Kolmogorov complexity"
  sources := [
    { paper := ShenUspenskyVereshchagin2017, theorem := unverified,
      locator := "Sections 2.2 and 2.3" }
  ]
  theorems := [
    Cslib.Kolmogorov.DescriptionMethod.exists_complexity_universal_add_condUniversal_le,
    Cslib.Kolmogorov.DescriptionMethod.exists_abs_complexity_universal_pair_sub_le,
    Cslib.Kolmogorov.exists_abs_algorithmicInformation_sub_le,
    Cslib.Kolmogorov.exists_abs_algorithmicInformation_sub_algorithmicInformation_le
  ]
  scope := "Plain complexity of the Partrec universal method on natural numbers, pairs coded by \
    Nat.pair, and log the binary length Nat.size. With k = C(x, y): C(x) + C(y | x) <= \
    k + 2 log k + 4 log log k + O(1), |C(x, y) - C(x) - C(y | x)| <= 6 log k + O(1), and \
    |I(x : y) - I(y : x)| <= 12 log k + O(1). Exact prefix-complexity symmetry and \
    time-bounded symmetry are not formalized."

register_result "minkt-np" where
  title := "MINKT, the time-bounded Kolmogorov complexity problem, is in NP"
  topic := "meta-complexity"
  sources := [
    { paper := Ko1991, theorem := unverified, locator := unverified },
    { paper := Hirahara2018, theorem := unverified, locator := "Definition 9" },
    { paper := LiuPass2020, theorem := unverified, locator := "Section 2.2" }
  ]
  theorems := [
    Cslib.Kolmogorov.MINKT.mem_NP,
    Cslib.Kolmogorov.MINKTAt.mem_NP,
    Cslib.Kolmogorov.MINKTAt.mem_NP_polynomial₂
  ]
  scope := "Instances are a string with time and size thresholds in unary, and K^t is measured \
    with the library's multi-tape universal machine and step clock. Fixed thresholds t and s \
    computable in polynomial time in unary give an NP bit-string language. Membership only; \
    NP-hardness of MINKT is not formalized. Hirahara's Definition 9 (after Ko) defines the \
    problem, and the fixed-threshold MINKTAt follows Liu and Pass, Section 2.2."

register_result "minktstar-rp-hard" where
  title := "Hirahara: MINKT* is NP-hard under randomized reductions"
  topic := "meta-complexity"
  sources := [
    { paper := Hirahara2022, theorem := "Theorem I.2",
      locator := "p. 971, \"In particular\"" }
  ]
  theorems := [
    Cslib.Kolmogorov.MINKTStar.rpHard,
    Cslib.Kolmogorov.MINKTStar.rpReducible_GapCMMSA_MINKTStar,
    Cslib.Kolmogorov.MINKTStar.NP_subset_BPP_of_mem_BPP,
    Cslib.Kolmogorov.MINKTStar.NP_subset_coRP_of_mem_coRP
  ]
  scope := "Every NP language reduces to MINKT* (a partial string over {0, 1, *}, then the step \
    budget and the size threshold in unary) by a polynomial-time randomized many-one reduction \
    with one-sided error: yes maps to yes always, no to no with probability at least 2/3. K^t \
    counts the steps of the described machine under the library's multi-tape universal machine, \
    where the source's footnote 6 uses a KT-style measure. Library route: from the library's \
    GapCMMSA Δ g 1 (NP-hard via label cover) by the seeded construction of the partial MCSP \
    reduction, with a polynomial-time generator for the yes side and a count of truth tables of \
    small time-bounded complexity for the no side; the source fixes the statement, not the \
    proof. The (log N)^ε inapproximability and distributional forms of Theorem I.2 are not \
    formalized. The BPP and coRP inclusions are conditional on MINKT* being in BPP or coRP; they \
    follow from the reduction and are not stated separately in the source."

register_result "mktp-exp" where
  title := "MKtP, the minimum Levin Kt complexity problem, is in E and EXP"
  topic := "meta-complexity"
  sources := [
    { paper := LiuPass2021Crypto, theorem := unverified, locator := "Section 2.2" }
  ]
  theorems := [
    Cslib.Kolmogorov.MKtP.mem_E,
    Cslib.Kolmogorov.MKtP.mem_EXP,
    Cslib.Kolmogorov.MKtPAt.mem_EXP
  ]
  scope := "Levin's Kt for the library's multi-tape universal machine. The threshold is \
    encoded in unary, where Liu and Pass use a binary threshold of about log n bits; for \
    thresholds O(|x|) the two encodings are polynomially related. MKtPAt s, with s \
    computable in polynomial time in unary, is in EXP over bit strings. Membership only."

register_result "tfnp-eopl-eq-sopl-inter-ppad" where
  title := "EOPL = SOPL ∩ PPAD"
  topic := "structural complexity"
  sources := [
    { paper := GoosEtAl2022, theorem := "Lemma 4",
      locator := "Section 5, pp. 9–10 of arXiv:2202.07761v2" }
  ]
  theorems := [
    Cslib.Complexity.EOPL_eq_SOPL_inter_PPAD,
    Cslib.Complexity.SOPL_inter_PPAD_subset_EOPL,
    Cslib.Complexity.mem_EOPL_of_sinkOfPotentialLine_endOfLine
  ]
  scope := "Uniform total-search classes over any injective encoding enc : α ↪ List Bool, \
    defined by native deterministic multi-tape polynomial-time predecessor, successor and \
    binary potential families with unary vertex width and polynomial-time search reductions. \
    Potential-line graphs prune active edges along which the potential does not strictly \
    increase. Combines an end-of-line family directly with a sink-of-potential-line family \
    rather than routing through bijective pigeonhole."

register_result "tfnp-sopl-eopl-collapse" where
  title := "Further collapses in TFNP: SOPL = PLS ∩ PPADS and EOPL = PLS ∩ PPAD"
  topic := "structural complexity"
  sources := [
    { paper := GoosEtAl2022, theorem := "Theorem 1 and Theorem 2",
      locator := "Section 1, p. 1; Lemmas 2–3, Sections 3–4, pp. 6–8 of arXiv:2202.07761v2" }
  ]
  theorems := [
    Cslib.Complexity.SOPL_eq_PLS_inter_PPADS,
    Cslib.Complexity.EOPL_eq_PLS_inter_PPAD,
    Cslib.Complexity.PLS_inter_PPADS_subset_SOPL,
    Cslib.Complexity.PLS_inter_PPAD_subset_EOPL,
    Cslib.Complexity.mem_SOPL_of_localOpt_sinkOfLine
  ]
  scope := "Uniform total-search classes over any injective encoding enc : α ↪ List Bool, \
    defined by native deterministic multi-tape polynomial-time local-search, sink-of-line, \
    end-of-line and potential-line families with unary vertex width and polynomial-time search \
    reductions. Proves PLS ∩ PPADS ⊆ SOPL via the path-pigeonhole gadget and reversible PLS \
    transitions on width n₁(a) + 2(n₁(a) + n₂(a)), then deduces SOPL = PLS ∩ PPADS and \
    EOPL = PLS ∩ PPAD via EOPL = SOPL ∩ PPAD and PPAD ⊆ PPADS. UEOPL and query separations \
    are not formalized."

register_result "tfnp-eopl-sopl-promised-normalization" where
  title := "Promised-source normalization for EOPL and SOPL (Fearnley et al. Definition 9)"
  topic := "structural complexity"
  sources := [
    { paper := FearnleyGordonMehtaSavani2020, theorem := "Definition 9",
      locator := "Section 2 (arXiv:1811.03841v1)" }
  ]
  theorems := [
    Cslib.Complexity.promisedPotentialLine_normalized,
    Cslib.Complexity.exists_normalizedPotentialBound,
    Cslib.Complexity.endOfPotentialLinePromisedRel_normalized_iff,
    Cslib.Complexity.sinkOfPotentialLinePromisedRel_normalized_iff,
    Cslib.Complexity.endOfPotentialLineRel_searchReducible_promised_normalized,
    Cslib.Complexity.promised_normalized_searchReducible_endOfPotentialLineRel,
    Cslib.Complexity.endOfPotentialLineViolationRel_searchReducible_promised_normalized,
    Cslib.Complexity.mem_EOPL_iff_promised_bounded,
    Cslib.Complexity.mem_SOPL_iff_promised_bounded
  ]
  scope := "Uniform polynomial-time (n + 1)-bit normalization for EOPL and SOPL families over \
    any injective encoding enc : α ↪ List Bool, enforcing P(0^(n+1)) = 0^(n+1) ≠ S(0^(n+1)) and \
    V(0^(n+1)) = 0 with V'(1 u) = V u + 1, unary potential bit-bound 2^(m + 1), pure (R1)/(R2) \
    solution relations without a failed-promise fallback, and failed-promise back-maps via \
    potentialLineBack. Presented on uniform families rather than canonical circuit codes; UEOPL \
    and CLS are not formalized."

register_result "edmonds-optimum-branchings" where
  title := "Edmonds: optimum branchings and minimum-cost spanning arborescences are in P"
  topic := "algorithms"
  sources := [
    { paper := Edmonds1967Branchings, theorem := "Theorem 1",
      locator := "Section 3 (Section 2 reduction, Section 4 algorithm and proof)" }
  ]
  theorems := [
    Cslib.Algorithms.Lean.Arborescence.computableInPolyTime_edmondsList,
    Cslib.Algorithms.Lean.Arborescence.computableInPolyTime_edmondsOutList,
    Cslib.Algorithms.Lean.Arborescence.computableInPolyTime_optimumBranchingList,
    Cslib.Algorithms.Lean.Arborescence.minArborescenceDec_mem_P,
    Cslib.Algorithms.Lean.Arborescence.minOutArborescenceDec_mem_P,
    Cslib.Algorithms.Lean.Arborescence.maxBranchingDec_mem_P
  ]
  scope := "Adjacency matrices in Boolean row-major tables and integer arc weights and \
    thresholds in binary (encIntBin); roots are binary naturals (encNat). Subtraction-free \
    contraction keeps intermediate table entries within (n + 1) ^ i · M₀, yielding native \
    multi-tape P deciders for bounded-cost spanning in- and out-arborescences and \
    bounded-weight branchings. Related O(n³) TimeM bounds and weight-shift reductions live \
    in the sibling Arborescence.Table and Arborescence.Branching modules; Edmonds' Theorem 2 \
    (the branching polytope) and sparse O(m log n) / O(m + n log n) implementations are not \
    formalized."
register_result "simhash" where
  title := "Charikar's SimHash collision law"
  topic := "algorithms"
  sources := [
    { paper := Charikar2002, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Probability.measureCollisionProb_simHash,
    Cslib.Probability.measureCollisionProb_simHash_of_norm_eq_one,
    Cslib.Probability.isLocalitySensitive_simHash_inner
  ]
  scope := "Random-hyperplane sign hash `simHash r u = decide (0 <= <u, r>)` with seed `r` \
    drawn from the standard Gaussian measure `stdGaussian E` on a finite-dimensional real \
    inner product space `E` (and i.i.d. `gaussianReal 0 1` coordinates on `EuclideanSpace`). \
    Proves exact collision probability `1 - angle u v / pi` on nonzero vectors, cosine-similarity \
    sensitivity on unit vectors, and Charikar's triangle inequality for measurable collision laws."

register_result "angular-near-neighbor" where
  title := "Approximate near neighbours in angular distance via SimHash"
  topic := "algorithms"
  sources := [
    { paper := Charikar2002, theorem := unverified, locator := unverified },
    { paper := IndykMotwani1998, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.DataStructure.NearNeighbor.rho_simHash_le,
    Cslib.DataStructure.NearNeighbor.measureReal_query_simHash_eq_none_le
  ]
  scope := "Static `(c, theta)`-approximate near-neighbour query bound over `Measure.pi` tables of \
    `k = numHashes` AND-composed SimHash bits (`L = numTables`, stopping rule `T = 3 * L`). \
    Proves exponent `rho <= 1 / c` and failure probability at most `exp (-1) + 1 / 3` whenever \
    `0 < theta`, `1 < c`, and `c * theta < pi`. Probabilistic query failure only; word-RAM hash \
    buckets, seed storage, dynamic updates, and query runtime are not formalized."

register_result "p-stable-lsh" where
  title := "p-stable LSH collision probabilities for p = 1 and p = 2"
  topic := "algorithms"
  sources := [
    { paper := DatarImmorlicaIndykMirrokni2004, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Probability.measureCollisionProb_p2StableHash,
    Cslib.Probability.p2StableProb_eq_integral,
    Cslib.Probability.measureCollisionProb_p1StableHash,
    Cslib.Probability.p1StableProb_eq
  ]
  scope := "Shifted interval quantization `floor ((proj a x + b) / r)` with `b` drawn from \
    `uniformInterval r`. Proves the general Fubini integral, Cauchy `1`-stability for i.i.d. \
    `cauchyMeasure 0 1` projections, exact Euclidean (`p = 2`, Gaussian) and `l_1` (`p = 1`, \
    Cauchy) collision formulas including Datar et al.'s integral representation and closed \
    forms, strict positivity, and strict monotonicity. General `p` in `(0, 2) \\ {1, 2}` is \
    not formalized."

register_result "p-stable-near-neighbor" where
  title := "Approximate near neighbours in l_2 and l_1 via p-stable LSH"
  topic := "algorithms"
  sources := [
    { paper := DatarImmorlicaIndykMirrokni2004, theorem := unverified, locator := unverified },
    { paper := HarPeledIndykMotwani2012, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.DataStructure.NearNeighbor.rho_p2Stable_lt_one,
    Cslib.DataStructure.NearNeighbor.measureReal_query_p2Stable_eq_none_le,
    Cslib.DataStructure.NearNeighbor.rho_p1Stable_lt_one,
    Cslib.DataStructure.NearNeighbor.measureReal_query_p1Stable_eq_none_le
  ]
  scope := "Static `(c, d)`-approximate near-neighbour guarantees over `Measure.pi` AND tables \
    for Euclidean distance (`p = 2`, `stdGaussian E`) and `l_1` distance (`p = 1`, product \
    `cauchyMeasure 0 1`), proving sublinear `rho < 1` and query failure at most `exp (-1) + 1 / 3` \
    when `0 < w`, `0 < d`, and `1 < c`. Probabilistic query failure only; word-RAM hash buckets, \
    seed storage, dynamic updates, and query runtime are not formalized."

register_result "goemans-williamson-max2sat" where
  title := "Goemans–Williamson α-approximation rounding for MAX-2SAT (α > 0.87856)"
  topic := "algorithms"
  sources := [
    { paper := GoemansWilliamson1995, theorem := "Theorem 7.2.1.1",
      locator := "Section 7.2.1" }
  ]
  theorems := [
    Cslib.Algorithms.Lean.MaxTwoSAT.goemansWilliamsonConstant_mul_signedSdpValue_le_integral,
    Cslib.Algorithms.Lean.MaxTwoSAT.goemansWilliamsonConstant_mul_satSdpValue_le_integral,
    Cslib.Algorithms.Lean.MaxTwoSAT.goemansWilliamsonConstant_mul_satValue_le_integral
  ]
  scope := "Exact stdGaussian random-hyperplane rounding of unit-vector SDP relaxations (P') \
    and weighted MAX-2SAT over arbitrary finite clause/variable types with nonnegative weights, \
    using Real.goemansWilliamsonConstant (0.87856 < α). No SDP solver, Gaussian sampler, \
    derandomization, or Section 7.2.2 MAX-SAT LP/SDP hybrid is formalized."

register_result "goemans-williamson-max2sat-cnf" where
  title := "Goemans–Williamson rounding bridge for Cslib MaxTwoSAT CNFs"
  topic := "algorithms"
  sources := [
    { paper := GoemansWilliamson1995, theorem := "Section 7.2.1",
      locator := "Section 7.2.1" }
  ]
  theorems := [
    Cslib.Algorithms.Lean.MaxTwoSAT.goemansWilliamsonConstant_mul_countP_le_integral,
    Cslib.Algorithms.Lean.MaxTwoSAT.goemansWilliamsonConstant_mul_target_le_integral_of_mem
  ]
  scope := "Specialization of Goemans–Williamson MAX-2SAT random-hyperplane rounding to list \
    CNFs counted by Cslib.Logic.PL.CNF.countP and membership in Cslib.Complexity.MaxTwoSAT \
    under exact stdGaussian expectation; no polynomial-time SDP solver is included."

open Cslib.Algorithms.Lean.MaxDicut in
register_result "goemans-williamson-maxdicut" where
  title := "Goemans–Williamson β-approximation rounding for MAX-DICUT (β > 0.79607)"
  topic := "algorithms"
  sources := [
    { paper := GoemansWilliamson1995, theorem := "Lemma 7.3.1, Lemma 7.3.2",
      locator := "Section 7.3, pp. 1138–1139" }
  ]
  theorems := [
    goemansWilliamsonDicutConstant_mul_dicutSdpValue_le_integral,
    goemansWilliamsonDicutConstant_mul_dicutValue_le_integral,
    goemansWilliamsonConstant_mul_sub_le_integral_of_isBalancedDigraph
  ]
  scope := "Exact stdGaussian random-hyperplane rounding for triple SDP relaxations (P'') and \
    weighted directed multigraphs with nonnegative weights, achieving \
    Real.goemansWilliamsonDicutConstant (0.79607 < β < 0.79608), plus the balanced-digraph \
    reduction recovering α > 0.87856 on p. 1138. No SDP solver, finite-precision sampler, or \
    derandomization is formalized."

register_result "binary-linear-constraint-operator-solution-perfect" where
  title := "Cleve–Mittal: finite-dimensional operator solutions of binary linear constraint \
    systems give perfect strategies"
  topic := "quantum complexity"
  sources := [
    { paper := CleveMittal2014,
      theorem := "unnumbered construction of a perfect strategy from an operator solution",
      locator := "§2, printed p. 3 (arXiv:1209.2729v1)" }
  ]
  theorems := [
    Cslib.PCP.LinearSystem.OperatorSolution.commutingWinProb_maxEntangledStrategy
  ]
  scope := "Binary linear (parity) constraint systems over finite variable and equation types, \
    with an arbitrary question distribution on pairs of an equation and a variable (the source \
    asks a uniformly random equation and one of its variables). For every operator solution in \
    M_ι(ℂ), ι finite and nonempty, the maximally entangled transpose strategy (X_v ⊗ 1 for \
    Alice, 1 ⊗ X_vᵀ for Bob) wins with probability 1, as a commuting-operator strategy on the \
    matrix algebra of ℂ^ι ⊗ ℂ^ι with the vector state of the maximally entangled state. The \
    source treats general Boolean predicates; the converse (its Theorem 1) is separate."

register_result "quantum-value-adversary" where
  title := "Ambainis: relational quantum adversary bound for non-Boolean input alphabets"
  topic := "quantum complexity"
  sources := [
    { paper := Ambainis2002, theorem := "Theorem 6",
      locator := "Section 6.1 (arXiv:quant-ph/0002066v1)" }
  ]
  theorems := [
    Cslib.Quantum.norm_inner_valueOracle_valueOracle_ge,
    Cslib.Quantum.one_sub_mul_sum_le_of_sq_le_value,
    Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_mul_sqrt_value,
    Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt_value,
    Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt_value_measureOut
  ]
  scope := "T-query quantum value-query algorithms over an arbitrary finite index type ι, \
    arbitrary input alphabet α, finite value register V, finite workspace W, and arbitrary \
    unitary oracle family step : α → (ℂ^V ≃ₗᵢ[ℂ] ℂ^V), with multi-outcome classical readout \
    out : ι × V × W → β (both measureProb and PMF measureOut forms). Proves exact factor 2 \
    without two-value diagonalization overhead: (1 - δ) √(m m') <= 2T √L and \
    (1 - 2√(ε(1-ε))) √(m m') <= 2T √L."

register_result "quantum-permutation-inversion" where
  title := "Ambainis: Ω(√N) quantum query lower bound for inverting a permutation"
  topic := "quantum complexity"
  sources := [
    { paper := Ambainis2002, theorem := "Theorem 7",
      locator := "Section 6.2 (arXiv:quant-ph/0002066v1)" }
  ]
  theorems := [
    Cslib.Quantum.one_sub_mul_sqrt_min_le_of_permInversion_partition,
    Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_div_two_le_of_permInversion,
    Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_div_two_le_of_permInversion_measureOut,
    Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_sub_one_le_of_permInversion,
    Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_card_le_of_permInversion,
    Cslib.Quantum.permInversion_div_two_lower_bound,
    Cslib.Quantum.permInversion_lower_bound,
    Cslib.Quantum.permInversion_measureOut_lower_bound
  ]
  scope := "T-query quantum value-query algorithms over a finite index type ι, finite value \
    register V, finite workspace W, and arbitrary unitary oracle family step : ι → (ℂ^V ≃ₗᵢ[ℂ] \
    ℂ^V), outputting π.symm target via a classical readout out with failure probability at most \
    ε <= 1/2 on every permutation π : Equiv.Perm ι. Proves (1 - 2√(ε(1-ε))) √⌊|ι|/2⌋ <= 2T, \
    (1 - 2√(ε(1-ε))) √(|ι| - 1) <= 2√2 T, and (for 2 <= |ι|) (1 - 2√(ε(1-ε))) √|ι| <= 2√3 T, \
    giving |ι| / 2 <= 1296 T² and |ι| <= 3888 T² at ε = 1/3."

register_result "nayak-wu-counting" where
  title := "Nayak–Wu: quantum query lower bound for approximate counting"
  topic := "quantum complexity"
  sources := [
    { paper := NayakWu1999, theorem := "Theorem 1.11",
      locator := "Section 1 (arXiv:quant-ph/9804066v2)" }
  ]
  theorems := [
    Cslib.Quantum.one_sub_mul_exactCount_le,
    Cslib.Quantum.one_sub_mul_approxCount_le,
    Cslib.Quantum.approxCount_lower_bound
  ]
  scope := "T-query bit-query quantum algorithm outputting a real estimate y with |y - t| < Δ \
    on inputs of Hamming weight t (failure probability at most ε, 2ε <= 1). When 1/2 <= Δ and \
    4Δ <= n, gives (1 - 2 sqrt(ε(1-ε))) (sqrt(n/Δ) + sqrt(t(n-t))/Δ) <= 16T and <= 288T at \
    ε = 1/3; when 0 < Δ <= 1/2 and 1 <= n, gives <= 4T. Derived from the adversary weight-layer \
    bound rather than polynomials. Relative counting and approximate mean are not formalized."

register_result "nayak-wu-kth-smallest" where
  title := "Nayak–Wu: quantum query lower bound for approximate k-th smallest selection"
  topic := "quantum complexity"
  sources := [
    { paper := NayakWu1999, theorem := "Theorem 1.5",
      locator := "Sections 1 and 2 (arXiv:quant-ph/9804066v2)" }
  ]
  theorems := [
    Cslib.Quantum.one_sub_mul_kthSmallest_le,
    Cslib.Quantum.kthSmallest_lower_bound,
    Cslib.Quantum.kthSmallest_involution_lower_bound,
    Cslib.Quantum.kthSmallest_index_lower_bound
  ]
  scope := "T-query value-query quantum algorithm over a finite index type and linearly ordered \
    alphabet returning an element within rank distance < Δ of k (or any relaxed value) with \
    failure probability at most ε <= 1/2, for 1 <= k <= n, 1 <= Δ, 4Δ <= n. Proves explicit \
    constants 32T (576T at ε = 1/3), 16T (288T) for involutive-difference oracle steps, and \
    the same bound on T + 1 for index-returning algorithms. Comparison-tree oracles are not \
    formalized."

register_result "nayak-wu-median" where
  title := "Nayak–Wu: quantum query lower bound for approximate median"
  topic := "quantum complexity"
  sources := [
    { paper := NayakWu1999, theorem := "Corollary 1.6",
      locator := "Section 1 (arXiv:quant-ph/9804066v2)" }
  ]
  theorems := [
    Cslib.Quantum.one_sub_mul_median_le,
    Cslib.Quantum.median_lower_bound,
    Cslib.Quantum.median_inv_delta_lower_bound,
    Cslib.Quantum.median_involution_lower_bound,
    Cslib.Quantum.median_index_lower_bound
  ]
  scope := "T-query value-query quantum algorithm over a finite index type (1 <= n) and \
    linearly ordered alphabet outputting a δ-approximate median (0 < δ < 1) with failure \
    probability at most ε <= 1/2. Gives (1 - 2 sqrt(ε(1-ε))) min(1/δ, n) <= 24T, 432T at \
    ε = 1/3 (hence 1/δ <= 432T when 1 <= δ n), 12T (216T) for involutive-difference oracle \
    steps, and the same bound on T + 1 for index-returning algorithms. Derived via adversary \
    weight-layer bounds rather than polynomials; comparison-tree oracles are not formalized."

register_result "unique-games-perfect-completeness" where
  title := "Satisfiable unique games are in P"
  topic := "interactive proofs"
  sources := [
    { paper := Khot2010, theorem := unverified,
      locator := "Section 2.4, after Definition 2.4 (author copy, p. 6)" }
  ]
  theorems := [
    Cslib.Complexity.gapUniqueGames_one_mem_PromiseP,
    Cslib.Complexity.gapUniqueGames_one_mem_PromiseP_of_pos,
    Cslib.Complexity.gapUniqueGames_zero_mem_PromiseP,
    Cslib.Complexity.isUniqueGame_mem_P,
    Cslib.Complexity.satisfiable_uniqueGame_mem_P
  ]
  scope := "Native multi-tape PromiseP and P membership for each fixed finite alphabet Fin L \
    under Graph.encoding (encPi (encFinEnum (Fin L))), the encoding of UniqueGamesConjecture. \
    For 0 < L, label propagation over List.finRange L is certified by reading the final \
    table directly without constructing ℕ → Fin L closures at runtime. For L = 0, Fin 0 is \
    empty so every unique game vacuously has unsatVal = 0 and GapUniqueGames (Fin 0) 1 s \
    has no no-instances, while no graph is satisfiable. This fixes L rather than taking it \
    as part of the input."

register_result "gap-two-csp-boolean-promise-p" where
  title := "Boolean gapCSP is in polynomial time"
  topic := "interactive proofs"
  sources := [
    { paper := Goldreich2007DraftR5, theorem := "Exercise 9.24",
      locator := "r5.pdf; PDF page 70 / printed page 452; Definition 9.18 checked" }
  ]
  theorems := [
    Cslib.Complexity.mem_PromiseP_of_satisfiable_bool
  ]
  scope := "Every promise problem on Boolean constraint graphs under Graph.encoding \
    encConstraintTable whose yes-instances are satisfiable and whose no-instances are \
    unsatisfiable is in PromiseP, with a uniform deterministic polynomial-time decider and no \
    randomness. This covers gapCSP^{0,1}_τ for every positive threshold function τ without \
    computing τ. The reduction is Graph.toCNF with one bit per label, producing a width-two \
    CNF satisfiable exactly when the graph is, decided by TwoSAT.mem_P. Instances need not be \
    well-formed: vertices are natural numbers and malformed vertex counts are admitted, a \
    larger promise. For well-formed graphs over a nonempty alphabet, \
    Graph.unsatVal_toFiniteGraph identifies the library unsatVal with the minimum over \
    assignments of the declared vertices. Outside-fleet source check: \
    https://github.com/cslib-community/cslib-frontier/pull/6367#pullrequestreview-5950754049"

register_result "arora-barak-dyadic-prefix-recovery" where
  title := "Polynomial-time rational recovery from a binary prefix"
  topic := "algorithms"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 20, Exercise §11",
      locator := "2007-01-08 public draft, printed p. 432 / PDF p. 448" }
  ]
  theorems := [Rat.recoverDyadicLogSq_eq_some, Rat.recoverDyadicLogSq_polyTime]
  scope := "Rounds upward after doubling the logarithm. For positive denominator bound N, \
    the precision is Nat.clog 2 (N ^ 2) fractional bits. The binary input encodes N and \
    the half-open dyadic cell index, including the integer part for improper fractions. \
    Terminating binary expansions use trailing zeros. The optional rational output uses \
    a reduced binary numerator and denominator. The native multitape polynomial-time \
    certificate covers the same decoder used in the recovery theorem."

register_result "bareiss-rational-elimination" where
  title := "Exact rational Bareiss–Jordan Gaussian elimination and entry bounds"
  topic := "algorithms"
  sources := [
    { paper := Schrijver1986,
      theorem := "Theorem 3.2; Theorem 3.3; Corollary 3.3a; Equations (28)–(30)",
      locator := "Section 3.2, pp. 29–30; Section 3.3, pp. 32–35" }
  ]
  theorems := [
    Cslib.LinearAlgebra.rationalElim_spec,
    Cslib.LinearAlgebra.ratRref_isReducedRowEchelon,
    Cslib.LinearAlgebra.ratRank_eq,
    Cslib.LinearAlgebra.ratSolve_spec,
    Cslib.LinearAlgebra.rationalElim_entry_bounds,
    Cslib.LinearAlgebra.ratSolve_entry_bounds
  ]
  scope := "Executable row-denominator-cleared fraction-free Bareiss–Jordan elimination over ℚ \
    built on Sylvester–Bareiss minor elimination over ℤ (RREF, exact rank, linearly independent \
    spanning row and kernel bases, canonical linear system solving, and Hadamard/factorial entry \
    and denominator bit-length bounds via stageEntryBound). Local adaptation: clears row \
    denominators upfront and tracks fraction-free minor-scaled Jordan updates with a \
    factorial/Hadamard bound rather than Schrijver's normalized rational elimination \
    (Section 3.3, pp. 32–35). Bounded milestone of Issue #3672 (circulant spectra and fibre-sum \
    bounds remain open there)."

register_result "bareiss-rational-elimination-polytime" where
  title := "Polynomial-time multi-tape Turing certificates for rational Gaussian elimination"
  topic := "algorithms"
  sources := [
    { paper := Schrijver1986,
      theorem := "Theorem 3.3; Corollary 3.3a (ii), (iv), (v)",
      locator := "Section 3.3, pp. 32–35" }
  ]
  theorems := [
    Cslib.LinearAlgebra.rationalElim_computableInPolyTime,
    Cslib.LinearAlgebra.ratRref_computableInPolyTime,
    Cslib.LinearAlgebra.ratRank_computableInPolyTime,
    Cslib.LinearAlgebra.ratRowBasis_computableInPolyTime,
    Cslib.LinearAlgebra.ratKernelBasis_computableInPolyTime,
    Cslib.LinearAlgebra.ratSolve_computableInPolyTime
  ]
  scope := "Native Turing.MultiTapeTM.ComputableInPolyTime certificates for rationalElim, \
    ratRref, ratRank, ratRowBasis, ratKernelBasis, and ratSolve. Local adaptations: uses \
    row-denominator-cleared fraction-free Bareiss–Jordan integer updates and structured \
    enc_structure codecs with explicit unary matrix dimensions and framed signed-binary/rational \
    entries to certify native multi-tape time and workspace bounds unconditionally (including on \
    ragged or oversized-header inputs), whereas Schrijver Section 3.3 analyzes normalized \
    rational elimination in binary input encoding size. Bounded milestone of Issue #3672 \
    (circulant spectra and fibre-sum bounds remain open there)."

register_result "kosaraju-scc" where
  title := "Kosaraju's linear-time strongly connected components and condensation order"
  topic := "algorithms"
  sources := [
    { paper := CLRS2009, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Algorithms.Lean.DFS.isSCCCondensation_sccs,
    Cslib.Algorithms.Lean.DFS.time_sccsM_of_nodup,
    Cslib.Algorithms.Lean.DFS.IsSCCCondensation.indexComponents_eq_iff,
    Cslib.Algorithms.Lean.DFS.IsSCCCondensation.indexComponents_le_of_edge
  ]
  scope := "Two-pass Kosaraju SCC decomposition on adjacency lists adj : V → List V in TimeM, \
    returning duplicate-free mutual-reachability components in forward condensation topological \
    order at exact cost 3 * (|vs| + ∑ v, |adj v|) for duplicate-free vertex lists covering V, \
    plus O(|V|) component-index lookup. Visited-set membership, insertion, and function-update \
    array steps are counted as unit-cost operations."

register_result "selected-entries-subset-convolution-timem" where
  title := "Selected entries of ranked subset convolution by the trimmed fast zeta transform"
  topic := "algorithms"
  sources := [
    { paper := ChanItakuraMaYu2026, theorem := "Theorem 2.2",
      locator := "Section 2.1, p. 5" }
  ]
  theorems := [
    Cslib.Algorithms.Lean.TrimmedYates.ret_solveM,
    Cslib.Algorithms.Lean.TrimmedYates.time_solveM
  ]
  scope := "TimeM unit-cost model (one tick per table cell; enumeration and dictionary \
    construction uncharged), not Word-RAM time. Inputs are look-up functions, so the paper's n \
    term for storing the input sets is absent; the bound 3 (d + 1) (sum_{j <= s} (d choose j) + \
    |queries| sum_{s <= j <= 2t} (2t choose j)) is exact. Weights in a commutative ring."

register_result "twosat-linear-timem" where
  title := "Aspvall–Plass–Tarjan linear-time 2-SAT solver and witness construction in TimeM"
  topic := "algorithms"
  sources := [
    { paper := AspvallPlassTarjan1979, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Algorithms.Lean.TwoSAT.solve_eq_some,
    Cslib.Algorithms.Lean.TwoSAT.isSome_solve_iff,
    Cslib.Algorithms.Lean.TwoSAT.time_solveFinM_le,
    Cslib.Algorithms.Lean.TwoSAT.isSome_solveNat_iff
  ]
  scope := "Linear-time 2-SAT decision and satisfying-assignment construction via Kosaraju SCCs \
    of the implication graph in TimeM (at most 12 * n + 8 * |φ| + 1 steps on CNF (Fin n)), \
    together with variable compaction connecting solveNat to Cslib.Complexity.TwoSAT."

register_result "twosat-polytime" where
  title := "Native multi-tape polynomial-time 2-SAT decision and witness construction"
  topic := "computational complexity"
  sources := [
    { paper := AspvallPlassTarjan1979, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.TwoSAT.mem_P,
    Cslib.Complexity.TwoSAT.eval_assignment_of_mem,
    Cslib.Complexity.TwoSAT.computableInPolyTime_solve,
    Cslib.Complexity.TwoSAT.computableInPolyTime_assignment
  ]
  scope := "Multi-tape Turing-machine polynomial-time decision and satisfying-assignment \
    construction for Cslib.Complexity.TwoSAT under binary CNF encoding encCNF, using \
    occurrence-bounded implication-graph reachability without dense variable-index arrays."

register_result "hornsat-least-model" where
  title := "Least-model characterization and non-uniqueness for HornSAT"
  topic := "computational complexity"
  sources := [
    { paper := Papadimitriou94, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.HornSAT.assignment_le_of_eval,
    Cslib.Complexity.HornSAT.isLeast_assignment,
    Cslib.Complexity.HornSAT.exists_multiple_models
  ]
  scope := "Forward-chaining HornSAT.assignment computes the pointwise-least satisfying model \
    of every satisfiable Horn formula, together with an explicit Horn formula admitting \
    distinct satisfying assignments on its occurring variables."
register_result "sperner-2d-ppad-completeness" where
  title := "PPAD-completeness of circuit two-dimensional Sperner (Sperner2D)"
  topic := "structural complexity"
  sources := [
    { paper := ChenDeng2006, theorem := unverified,
      locator := unverified },
    { paper := ChenDengTeng2009, theorem := unverified,
      locator := "Section 4.1, Definitions 4.2, 4.4 and 4.5 (with d = 2)" }
  ]
  theorems := [
    Cslib.Complexity.EndOfLine_searchReducible_Sperner2D,
    Cslib.Complexity.Sperner2D_searchHard,
    Cslib.Complexity.Sperner2D_searchComplete
  ]
  scope := "Explicit polynomial-time search reduction EndOfLine ≤ Sperner2D compiling each \
    n-bit EndOfLine instance uniformly into a circuit on a 2^(n + 5) × 2^(n + 5) grid of 16 × 16 \
    routing, crossover and end-tile gadgets, combined with Sperner2D_mem_PPAD under encSperner2D. \
    Sperner2D fixes the boundary colouring rather than taking a circuit-enforced boundary promise \
    as in discrete Brouwer; two-dimensional discrete Brouwer, three-dimensional Sperner \
    completeness and d-dimensional circuit Sperner are not formalized."

register_result "branching-vector-recurrence" where
  title := "Search-tree branching-vector recurrences and separated node-work bounds"
  topic := "exact exponential algorithms"
  sources := [
    { paper := FominKratsch2010, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.BranchingVector.BranchingRecurrence.le_mul_pow,
    Cslib.BranchingVector.BranchingTree.leafCount_le_pow,
    Cslib.BranchingVector.BranchingTree.workCost_le_mul_pow,
    Cslib.BranchingVector.charSum_fibonacci,
    Cslib.BranchingVector.charSum_prefixSteps_le_one
  ]
  scope := "Positive integer decrease vectors steps = [a₁, …, a_b] with characteristic sum \
    charSum steps r = ∑ r ^ (-aᵢ) <= 1 (1 <= r): T n <= C * r ^ n for recurrences with \
    T n <= max C (sum of T (n - d) over d in steps with d <= n) at every n and C >= 0; \
    leaf count <= r ^ measure s, node count <= (measure s + 1) * r ^ measure s, and separated \
    per-node overhead workCost <= W * (measure s + 1) * r ^ measure s on multi-way search trees \
    (1 <= r), plus closed-form Fibonacci ((1 + sqrt 5) / 2) and prefix [1, …, k] (2 - (1 / 2) ^ k) \
    factors."

register_result "cnf-prefix-branching" where
  title := "Disjoint clause-prefix SAT branching and model-count conservation"
  topic := "SAT algorithms"
  sources := [
    { paper := FominKratsch2010, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.PL.CNF.not_partitionsModels_clauseCoverBranches_two,
    Cslib.Logic.PL.CNF.modelCountOn_eq_sum_clausePrefixTree_leaves,
    Cslib.Logic.PL.CNF.satisfiable_iff_exists_clausePrefixTree_leaf,
    Cslib.Logic.PL.CNF.leafCount_clausePrefixTree_le,
    Cslib.Logic.PL.CNF.leafCount_clausePrefixTree_two_le
  ]
  scope := "Separates covering (CoversModels) and model-partitioning (PartitionsModels) CNF \
    branching rules, refutes model partitioning for naive two-literal clause covers, and proves \
    that disjoint clause-prefix branching on width-<= k CNFs conserves exact modelCountOn across \
    leaves with at most (2 - (1 / 2) ^ k) ^ n leaves (k >= 1) and ((1 + sqrt 5) / 2) ^ n leaves \
    at k = 2. Combinatorial search-tree specification; no native machine runtime asserted here."

register_result "schoening-multitape" where
  title := "Schöning: randomized k-SAT in time (2(k - 1)/k)^n on fair-coin multitape machines"
  topic := "SAT algorithms"
  sources := [
    { paper := Schoening1999, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.Schoening.half_mul_succeedProb_trial_le_fairTrial,
    Cslib.Complexity.Schoening.exists_multiTapePTM_KSAT,
    Cslib.Complexity.Schoening.exists_decidesWithBoundedErrorInTime_KSAT,
    Cslib.Complexity.Schoening.exists_decidesWithBoundedErrorInTime_ThreeSAT
  ]
  scope := "For every fixed clause width k >= 3 and amplification parameter c : Nat, one \
    finite-control fair-coin MultiTapePTM on encCNF (CNF Nat) using w = 2n + k + 3 bits per \
    sampleModNat step and a binary encNat countdown over 2 * schoeningTrials k φ.numVars c trials \
    halts on every branch within C * (((2(k - 1))/k) ^ φ.numVars * (|encCNF φ| + 1) ^ E) steps \
    and C * (|encCNF φ| + 1) ^ E work-tape cells (toNTM.RunsInSpace), outputs PMF.pure [false] \
    outside KSAT k, and accepts every φ in KSAT k with probability >= 1 - exp(-c) (>= 2/3 at \
    c = 2, giving (4/3)^n on ThreeSAT)."

section
open Cslib.Communication

register_result "unique-disjointness-cover-lower-bound" where
  title := "Kaibel–Weltge: (3/2)^n rectangle-cover lower bound for unique disjointness"
  topic := "communication complexity"
  sources := [
    { paper := KaibelWeltge2015, theorem := "Theorem 1",
      locator := "Sections 2–3 (arXiv:1307.3543v6)" }
  ]
  theorems := [
    Nondeterministic.three_pow_le_two_pow_mul_coverNumber_uniqueDisjointnessRel,
    Nondeterministic.three_div_two_pow_le_of_coverNumber_uniqueDisjointnessRel_le,
    Nondeterministic.clog_ceil_div_le_ecomplexity_uniqueDisjointnessRel
  ]
  scope := "Exponential (3/2)^|alpha| lower bound on the 1-rectangle covering number and \
    ceil(log2 ceil((3/2)^|alpha|)) bound on N^1 communication complexity of uniqueDisjointnessRel \
    over subsets of a finite type alpha, via card_le_two_pow_of_isValidDisjointSet."

end

register_result "correlation-polytope-extension-complexity" where
  title := "Kaibel–Weltge: (3/2)^n extension-complexity lower bound for the correlation polytope"
  topic := "combinatorial optimization"
  sources := [
    { paper := KaibelWeltge2015, theorem := "Theorem 1",
      locator := "Section 2 (arXiv:1307.3543v6)" },
    { paper := FioriniMassarPokuttaTiwaryDeWolf2015, theorem := "Lemma 6 and Theorem 7",
      locator := "Section 3.2 (arXiv:1111.0837v4)" }
  ]
  theorems := [
    three_pow_le_two_pow_mul_extensionComplexity_corrPolytope,
    HasExtendedFormulation.three_div_two_pow_le_of_corrPolytope
  ]
  scope := "Over any linearly ordered field K and nonempty finite index type alpha, \
    extensionComplexity (corrPolytope K alpha) satisfies 3^|alpha| <= 2^|alpha| * xc and \
    (3/2 : F)^|alpha| <= r for every extended formulation with r inequalities, via the valid \
    inequalities 2 diag(a) - a a^T and the unique-disjointness cover bound."

register_result "cut-polytope-extension-complexity" where
  title := "FMPTW: exponential extension-complexity lower bound for the cut polytope"
  topic := "combinatorial optimization"
  sources := [
    { paper := DeSimone1990, theorem := unverified, locator := unverified },
    { paper := FioriniMassarPokuttaTiwaryDeWolf2015, theorem := "Theorems 5 and 7",
      locator := "Section 3.2 (arXiv:1111.0837v4)" },
    { paper := KaibelWeltge2015, theorem := "Theorem 1",
      locator := "Section 2 (arXiv:1307.3543v6)" }
  ]
  theorems := [
    extensionComplexity_cutPolytope_option_eq,
    three_pow_le_two_pow_mul_extensionComplexity_cutPolytope,
    HasExtendedFormulation.three_div_two_pow_le_of_cutPolytope
  ]
  scope := "Linear isomorphism between cutPolytope K (Option alpha) and corrPolytope K alpha, \
    yielding (3/2 : F)^(|V| - 1) <= r for every extended formulation of cutPolytope K V with \
    r inequalities over any finite vertex type V with |V| >= 2."

register_result "stable-set-polytope-extension-complexity" where
  title := "FMPTW: 2^{Omega(sqrt n)} extension-complexity lower bound for the stable-set polytope"
  topic := "combinatorial optimization"
  sources := [
    { paper := FioriniMassarPokuttaTiwaryDeWolf2015, theorem := "Lemma 8 and Theorem 10",
      locator := "Section 3.3 (arXiv:1111.0837v4)" },
    { paper := KaibelWeltge2015, theorem := "Theorem 1",
      locator := "Section 2 (arXiv:1307.3543v6)" }
  ]
  theorems := [
    extensionComplexity_corrPolytope_le_corrGadgetGraph,
    three_pow_le_two_pow_mul_extensionComplexity_stabPolytope,
    HasExtendedFormulation.three_div_two_pow_le_of_stabPolytope
  ]
  scope := "For every m >= 2, the explicit m-vertex graph stabHardGraph m (built from the \
    2 p^2-vertex gadget graph corrGadgetGraph p with p = Nat.sqrt (m / 2) and isolated padding) \
    satisfies (3/2 : F)^Nat.sqrt (m / 2) <= r for any extended formulation of \
    stabPolytope K (stabHardGraph m) with r inequalities."

register_result "tsp-polytope-extension-complexity" where
  title := "FMPTW: 2^{Omega(sqrt n)} extension-complexity lower bound for the TSP polytope"
  topic := "combinatorial optimization"
  sources := [
    { paper := FioriniMassarPokuttaTiwaryDeWolf2015, theorem := "Lemma 11 and Theorem 12",
      locator := "Section 3.4 (arXiv:1111.0837v4)" },
    { paper := KaibelWeltge2015, theorem := "Theorem 1",
      locator := "Section 2 (arXiv:1307.3543v6)" }
  ]
  theorems := [
    extensionComplexity_corrPolytope_le_tspPolytope_splitV,
    extensionComplexity_corrPolytope_le_tspHardGraph_face,
    three_pow_le_two_pow_mul_extensionComplexity_tspPolytope,
    HasExtendedFormulation.three_div_two_pow_le_of_tspPolytope
  ]
  scope := "Via the 3-SAT correlation digraph corrDigraphAdj (at most 23 p^2 vertices) and the \
    padded directed-to-undirected 3-split, corrPolytope K (Fin p) projects linearly from a face \
    of tspPolytope K V whenever |V| >= 69 with p = Nat.sqrt (|V| / 69), giving (3/2 : F)^p <= r \
    for every extended formulation of tspPolytope K V with r inequalities."
register_result "sturm-real-root-counting" where
  title := "Sturm's theorem for separable real polynomials"
  topic := "algebraic complexity"
  sources := [
    { paper := BasuPollackRoy2006, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Polynomial.sturmSeq_map,
    Polynomial.sturmVariations_sub_eq_card_roots_Ioc,
    Polynomial.sturmVariations_sub_eq_card_roots_Ioc_of_squarefree,
    Polynomial.sturmVariations_sub_eq_card_roots_Ioo,
    Polynomial.sturmVariations_sub_eq_card_roots_Icc
  ]
  scope := "Exact real-root counting on (a, b], (a, b), and [a, b] via Sturm sign variations of \
    sturmSeq p (derivative p) for separable (equivalently squarefree) p : ℝ[X], together with \
    field-homomorphism invariance of sturmSeq. Proved over ℝ via local constancy of \
    sturmVariations p x + #{r <= x} rather than general real closed fields."

register_result "mahler-mignotte-root-separation" where
  title := "Hadamard's determinant inequality and Mahler–Mignotte root-separation bounds"
  topic := "algebraic complexity"
  sources := [
    { paper := Mahler1964, theorem := unverified, locator := "pp. 257–262" },
    { paper := Mignotte1982, theorem := unverified, locator := "pp. 259–263" },
    { paper := BasuPollackRoy2006, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Matrix.hadamard_det_sq_le,
    Polynomial.mignotte_sep_mahler_complex,
    Polynomial.mignotte_sep_sqNorm_complex,
    Polynomial.mignotte_sep_sqNorm_real,
    Polynomial.mignotte_sep_sqNorm_rat
  ]
  scope := "Hadamard's determinant inequality over ℂ and Mahler–Mignotte root-separation lower \
    bounds 3 <= |α - β| ^ 2 * (d ^ (d + 2) * coeffSqNorm p ^ (d - 1)) for distinct roots of \
    separable integer and cleared-denominator rational polynomials of degree d >= 2, combining \
    Mahler's discriminant/Mahler-measure inequality with |discr p| >= 1 and Landau's l^2 bound."

register_result "certified-real-root-isolation" where
  title := "Certified Sturm-bisection real-root isolation with Mignotte depth and TimeM bounds"
  topic := "algorithms"
  sources := [
    { paper := BasuPollackRoy2006, theorem := unverified, locator := unverified },
    { paper := Mahler1964, theorem := unverified, locator := "pp. 257–262" },
    { paper := Mignotte1982, theorem := unverified, locator := "pp. 259–263" }
  ]
  theorems := [
    Cslib.RealRoot.isolateRootsTotal_isIsolatingFor,
    Cslib.RealRoot.isolateRootsTotal_pairwise_disjoint,
    Cslib.RealRoot.isolateRootsTotal_bijective_of_squarefree,
    Cslib.RealRoot.isolateRootsTotal_endpoint_bounds_of_bitBound,
    Cslib.RealRoot.isolateRootsTotalM_time_le_of_bitBound,
    Cslib.RealRoot.isolateRootsTotal_spec_of_eq,
    Cslib.RealRoot.isolatePolyRootsTotal_bijective,
    Cslib.RealRoot.isolatePolyRootsTotalM_time_le_of_bitBound
  ]
  scope := "End-to-end TimeM ℕ-charged Sturm-bisection real-root isolator over ℚ[X]: \
    isolateRootsTotalM / isolateRootsTotal on List ℚ is executable (decide +kernel / #eval), \
    charging all preprocessing (trim, Euclidean Sturm sequence, Cauchy bound, denominator \
    clearing, l^2 norm, and Nat.clog), bisection, left-root refinement, and Mignotte-fueled \
    boundary separation into strictly disjoint closed intervals (J₁.upper < J₂.lower), whereas \
    isolatePolyRootsTotalM / isolatePolyRootsTotal on Polynomial ℚ is noncomputable (inheriting \
    Polynomial's noncomputable Finsupp representation) and measures the TimeM ℕ cost of \
    isolateRootsTotalM on p.coeffsBelow (p.natDegree + 1) without charging coefficient extraction \
    from Polynomial ℚ. Certifies strict monotone bijection onto {x : ℝ // aeval x p = 0} for \
    every squarefree p : ℚ[X], dyadic endpoint numerator/denominator bit bounds, and O(n^5 (B+2)) \
    TimeM ℕ operation count under HasCoeffBitBound B cs. TimeM ℕ counts unit-cost algebraic/RAM \
    scalar operations on ℚ/ℤ/ℕ rather than bit-level Turing complexity along Euclidean Sturm \
    remainders."
register_result "yap-collapse" where
  title := "Yap's theorem: coNP in NP/poly collapses the polynomial hierarchy to Σ₃"
  topic := "structural complexity"
  sources := [
    { paper := Yap1983, theorem := unverified, locator := unverified },
    { paper := BodlaenderJansenKratsch2014, theorem := "Theorem 2",
      locator := "p. 6 (arXiv v1)" }
  ]
  theorems := [
    Cslib.Complexity.SigmaP_two_subset_NPPoly_of_coNP_subset_NPPoly,
    Cslib.Complexity.PiP_three_eq_SigmaP_three_of_coNP_subset_NPPoly,
    Cslib.Complexity.PH_eq_SigmaP_three_of_coNP_subset_NPPoly,
    Cslib.Complexity.PH_eq_SigmaP_three_of_UNSAT_mem_NPPoly,
    Cslib.Complexity.PH_eq_SigmaP_three_of_coNP_encBits_subset_NPPoly,
    Cslib.Complexity.PH_eq_SigmaP_three_inter_PiP_three_of_coNP_subset_NPPoly
  ]
  scope := "Conditional collapse for arbitrary injective instance encodings. NPPoly uses a \
    polynomially bounded bit-string advice function of the encoded input length read by a \
    native polynomial-time NP verifier; PH uses polynomial-time alternating verifiers with \
    exact polynomial block lengths. Under coNP ⊆ NP/poly (equivalently NP ⊆ coNP/poly, \
    coNP encBits ⊆ NPPoly encBits, or UNSAT ∈ NPPoly encCNF via Cook–Levin and the CNF \
    decoder), Σ₂ ⊆ NP/poly, Π₃ = Σ₃, and PH = Σ₃ = Σ₃ ∩ Π₃. General level-k advice collapses \
    from Σ_k ⊆ Π_k/poly are not part of this entry."
register_result "randomized-marking-paging" where
  title := "2 H_k-competitiveness of the randomized marking paging algorithm"
  topic := "algorithms"
  sources := [
    { paper := FiatKarpLubyMcGeochSleatorYoung1991,
      theorem := "Theorem 1",
      locator := "Section 3" }
  ]
  theorems := [
    Cslib.DataStructure.Paging.expectedCost_markingStrategy_eq,
    Cslib.DataStructure.Paging.trackerExpectedCost_le_harmonic_mul_cleanCount,
    Cslib.DataStructure.Paging.cleanCount_le_two_mul_scheduleCost,
    Cslib.DataStructure.Paging.markingStrategy_expectedCost_le,
    Cslib.DataStructure.Paging.markingStrategy_isCompetitive,
    Cslib.DataStructure.Paging.markingStrategy_expectedCost_toReal_le
  ]
  scope := "Proves that the randomized marking algorithm (markingStrategy k hk) in the \
    behavioural online strategy model (Online.BehavioralStrategy) is 2 H_k-competitive with \
    additive constant 0 against an oblivious adversary from any admissible initial cache \
    |s₀| ≤ k over any [DecidableEq α] page type. Local adaptations relative to \
    arXiv:cs/0205038v1 Section 3: allows arbitrary page types α, initializes from any |s₀| ≤ k \
    via non-evicting warmup while |cache| < k, and bounds clean requests by 2 * OPT directly \
    against arbitrary (not necessarily lazy) valid offline schedules."


register_result "quantum-weighted-adversaries" where
  title := "Weighted quantum adversary lower bounds (Alb₂ and Alb₃)"
  topic := "quantum complexity"
  sources := [
    { paper := Ambainis2006, theorem := "Lemma 1",
      locator := "Section 4.1 (arXiv:quant-ph/0305028v4)" },
    { paper := Zhang2005, theorem := "Theorem 3 and Theorem 5",
      locator := "Section 1 and Section 2 (arXiv:quant-ph/0311060v2)" }
  ]
  theorems := [
    Cslib.Quantum.WeightScheme.one_sub_mul_sum_le,
    Cslib.Quantum.WeightScheme.one_sub_two_mul_sqrt_mul_sum_le,
    Cslib.Quantum.WeightScheme.one_sub_mul_sqrt_le_of_load_le,
    Cslib.Quantum.WeightScheme.one_sub_two_mul_sqrt_mul_sqrt_le_of_load_le,
    Cslib.Quantum.WeightScheme.ofUnweighted_loadFst_le,
    Cslib.Quantum.WeightScheme.ofUnweighted_loadSnd_le
  ]
  scope := "T-query bit-query phase-oracle quantum algorithms over finite workspace, for general \
    promise relations (x, y) with P x ∧ P y ∧ f x ≠ f y and arbitrary finite output alphabets α \
    (using pairwise disjoint measurement regions S_out : α → Finset _). Covers nonnegative \
    WeightScheme (Ambainis's weighted adversary and Zhang's strong Alb₃ method), its reduction \
    from strong to weak load bounds, and the WeightScheme.ofUnweighted embedding used in \
    AmbainisAdversary.lean to derive the unweighted adversary bound (Alb₂). Spectral matrices \
    and negative weights are in SpectralAdversary.lean."

register_result "quantum-general-adversaries" where
  title := "Spectral and negative-weight quantum adversary lower bounds (ADV and ADV±)"
  topic := "quantum complexity"
  sources := [
    { paper := BarnumSaksSzegedy2003, theorem := unverified, locator := unverified },
    { paper := HoyerLeeSpalek2007, theorem := "Theorem 1 and Theorem 2",
      locator := "Section 1.1 (arXiv:quant-ph/0611054v2)" }
  ]
  theorems := [
    Cslib.Quantum.one_sub_mul_opNorm_le_spectral,
    Cslib.Quantum.one_sub_mul_spectralAdversary_le,
    Cslib.Quantum.one_sub_mul_opNorm_le_general_boolean,
    Cslib.Quantum.one_sub_mul_generalAdversary_le_boolean,
    Cslib.Quantum.one_sub_mul_opNorm_le_general,
    Cslib.Quantum.one_sub_mul_generalAdversary_le,
    Cslib.Quantum.spectralSensitivity_le_spectralAdversary,
    Cslib.Quantum.WeightScheme.le_spectralAdversary,
    Cslib.Quantum.spectralAdversary_le_generalAdversary,
    Cslib.Quantum.spectralAdversary_le_div_of_hammingDist_ge
  ]
  scope := "T-query bit-query phase-oracle quantum algorithms over finite workspace, for general \
    promise relations (x, y) with P x ∧ P y ∧ f x ≠ f y and arbitrary finite output alphabets α \
    (using pairwise disjoint measurement regions S_out : α → Finset _). Covers Barnum–Saks–Szegedy \
    spectral adversary ADV (norm quotient over nonnegative symmetric Γ, cited via HLS07 §1.1 since \
    CCC'03 was not directly inspected), Høyer–Lee–Špalek negative-weight adversary ADV± \
    (strengthened to (1 - 2√(ε(1-ε)) - ε) ADV± ≤ 2T and exact Boolean 1 - 2√(ε(1-ε))), the \
    hierarchy λ(f) ≤ ADV(f) ≤ ADV±(f) and Alb₃ ≤ ADV(f), and the Hamming-distance barrier \
    ADV(f) ≤ N / k. Non-Boolean input alphabets (value queries / permutation inversion) and \
    general composition theorems are not formalized here."

register_result "fujisaki-okamoto-bot-ind-cca" where
  title := "ROM IND-CCA security of the word-level explicit-rejection FO^⊥ KEM from IND-CPA of the \
    PKE family"
  topic := "cryptography"
  sources := [
    { paper := HofheinzHoevelmannsKiltz2017, theorem := "Theorems 3.2 and 3.3",
      locator := "§3.1 (Theorem 3.2, p. 12), §3.2.1 (Theorem 3.3, p. 14), §3.3 (p. 21; Fig. 18, \
        the FO^⊥ row of the bounds table and \"Concrete parameters\", p. 22), the §1.1.2 table \
        (p. 6) and the query-count convention of §2.1 (p. 9) (IACR ePrint 2017/604, version of \
        2 November 2021)" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.INDCPA.romINDCCABot
  ]
  scope := "Asymptotic, random oracle model; explicit-rejection FO^⊥ = U^⊥ ∘ T (HHK17 §3.3, \
    Fig. 18). Let P be a word-level PKE family (at parameter n: messages of length msgLen n, \
    uniform coins of length coinLen n, ciphertext space the words of length at most ctLen n) \
    that is efficient (uniform strict PPT key generation; polynomial-time encryption, decryption \
    and lengths), whose ciphertexts lie in its ciphertext space (CiphertextFits), that is \
    δ-correct (HHK17 §2.1, p. 7) with δ negligible and γ-spread (p. 8) with 2^{-γ(n)} negligible, \
    and with 2^{-msgLen n} negligible; let keyLen be polynomial-time. γ-spreadness is a \
    requirement of the source for FO^⊥ (§1.1.2 table, p. 6; Theorem 3.2), and the premises on \
    δ, γ and msgLen are the asymptotic form of its \"Concrete parameters\" (δ ≤ 2^{-κ}, γ ≥ κ, \
    |M| ≥ 2^κ; p. 22). If P is IND-CPA secure against uniform strict PPT adversaries \
    (single-challenge two-stage game of HHK17 Def. 2.2, both challenge messages of length \
    msgLen n), its FO^⊥ KEM with keys of length keyLen n is IND-CCA secure (HHK17 Def. 2.4 / \
    Fig. 4) against uniform strict oracle PPT adversaries with oracles G, H and decapsulation; \
    no premise bounds the number of queries. Encapsulation draws m uniformly from words of \
    length msgLen n, as in Fig. 18. G and H are lazily sampled random oracles on word domains, \
    and a request outside a domain gets the empty word. The key uses the canonical encoding \
    H(false, m, c) of HHK17's H(m, c). Decapsulation refuses the challenge ciphertext, \
    rejects words longer than ctLen n with ⊥, and treats decryption results of the wrong length \
    as ⊥. The advantage is the two-world difference between b = 0 and b = 1, twice HHK17's \
    |Pr[b' = b] - 1/2|. HHK17 state a concrete bound (the FO^⊥ row of the §3.3 table, p. 22: \
    q_RO(δ + 2^{-γ}) + 3q_RO/|M| + 3·Adv^{IND-CPA}(A')), counting every evaluation of G and H \
    in the experiment (§2.1, p. 9); this theorem states none. Its proof applies IND-CPA to the \
    explicit reduction romBotCpaReductionWord, certified uniform strict PPT \
    (IsEfficient.isPPT_romBotCpaReductionWord), through the per-parameter step \
    Scheme.indCcaBotAdvantage_le, whose bound 2·Adv^{IND-CPA} + 2(qG + qH)/|M| + \
    2(qG + qH + 1)δ + 2(qG + qH + qD)2^{-γ} counts the adversary's explicit queries and differs \
    from HHK17's in every term (neither implies the other); every term is negligible under the \
    premises. The proof composes the T and U^⊥ hops directly instead of through standalone \
    OW-PCVA, and gives no concrete runtime map."

register_result "fujisaki-okamoto-notbot-word-rom-ind-cca" where
  title := "ROM IND-CCA security of the word-level FO-notbot KEM from IND-CPA of the PKE family"
  topic := "cryptography"
  sources := [
    { paper := HofheinzHoevelmannsKiltz2017, theorem := "Theorems 3.2 and 3.4",
      locator := "§3.1 (Theorem 3.2, p. 12; remark closing its proof, p. 13), §3.2.2 \
        (Theorem 3.4, p. 16), §1.1.2 table (p. 6) and KEM-notbot row of the §3.3 bounds table \
        (p. 22) (IACR ePrint 2017/604, version of 2 November 2021)" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.INDCPA.romINDCCA
  ]
  scope := "Asymptotic, random oracle model; implicit-rejection FO-notbot = U-notbot ∘ T only. \
    Let P be a word-level PKE family (at parameter n: messages of length msgLen n, uniform coins \
    of length coinLen n, ciphertext space the words of length at most ctLen n) that is \
    efficient (uniform strict PPT key generation; polynomial-time encryption, decryption and \
    lengths), whose ciphertexts lie in its ciphertext space (CiphertextFits), and that is \
    δ-correct (HHK17 §2.1) with δ negligible and 2^{-msgLen n} negligible; let keyLen be \
    polynomial-time. If P is IND-CPA secure against uniform strict PPT adversaries \
    (single-challenge two-stage game of HHK17 Def. 2.2, both challenge messages of length \
    msgLen n), its FO-notbot KEM with keys of length keyLen n is IND-CCA secure (HHK17 Def. 2.4 \
    / Fig. 4) against uniform strict oracle PPT adversaries with oracles G, H and \
    decapsulation; no premise bounds the number of decapsulation queries. G and H are lazily \
    sampled random oracles on word domains, and a request outside a domain gets the empty word. \
    Key derivation and implicit rejection query the same H on (m, c) and (s, c), respectively, \
    as in HHK17 Fig. 12. Decapsulation refuses the challenge \
    ciphertext, rejects words longer than ctLen n with ⊥, and treats decryption results of the \
    wrong length as ⊥. The advantage is the two-world difference between b = 0 and b = 1, twice \
    HHK17's |Pr[b' = b] - 1/2|. As in the source, no γ-spreadness is assumed (§1.1.2 table, \
    p. 6; KEM-notbot row of the §3.3 table, p. 22): the composition uses Theorem 3.2 in its \
    OW-PCA form (remark closing its proof, p. 13). The proof composes the T and U-notbot hops \
    directly instead of through standalone OW-PCA, and applies IND-CPA to the explicit reduction \
    romCpaReductionWord, certified uniform strict PPT (IsEfficient.isPPT_romCpaReductionWord); \
    it gives no concrete runtime map. FO^⊥ is fujisaki-okamoto-bot-ind-cca."

register_result "cgks-pir-coalition-lower-bound" where
  title := "Chor–Goldreich–Kushilevitz–Sudan: coalition t-privacy and full-coalition \
    communication lower bound"
  topic := "cryptography"
  sources := [
    { paper := ChorGoldreichKushilevitzSudan1998, theorem := unverified,
      locator := "Sections 2.2, 2.4 and 5.1 (pp. 4–6 and 14 of the April 21, 1998 journal \
        version)" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PIR.Scheme.isTPrivate_one_iff,
    Cslib.Crypto.Protocols.PIR.Scheme.isTPrivate_iff_tuple,
    Cslib.Crypto.Protocols.PIR.Scheme.exists_injective_answers_of_card_le,
    Cslib.Crypto.Protocols.PIR.Scheme.card_le_communication_of_card_le,
    Cslib.Crypto.Protocols.PIR.HasTPrivateScheme.card_le_of_le
  ]
  scope := "One-round information-theoretic PIR over arbitrary payload types β (defaulting to \
    Bool) with perfect correctness and perfect t-privacy against coalitions of at most t servers \
    (equivalent at t = 1 to single-server IsPrivate and for every t to t-tuple query \
    independence; machine runtime in CGKS §2.4, p. 6 is not modeled). Generalizing CGKS §5.1 \
    (p. 14) from k = 1 to full coalitions |S| ≤ t, some joint query vector makes the combined \
    server answers determine the database, and any perfectly correct t-private Boolean scheme \
    with |S| ≤ t communicates at least |ι| bits."

register_result "cgks-pir-shamir" where
  title := "Chor–Goldreich–Kushilevitz–Sudan: explicit finite-field polynomial Shamir \
    t-private PIR schemes"
  topic := "cryptography"
  sources := [
    { paper := ChorGoldreichKushilevitzSudan1998, theorem := unverified,
      locator := "Sections 1.1, 2.2, 2.4 and 3.4 (pp. 1–2, 4–6 and 11 of the April 21, 1998 \
        journal version)" },
    { paper := Shamir1979, theorem := unverified, locator := "whole paper" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PIR.isCorrect_shamir,
    Cslib.Crypto.Protocols.PIR.isTPrivate_shamir,
    Cslib.Crypto.Protocols.PIR.not_isTPrivate_succ_shamir,
    Cslib.Crypto.Protocols.PIR.isCorrect_shamirCube,
    Cslib.Crypto.Protocols.PIR.isTPrivate_shamirCube,
    Cslib.Crypto.Protocols.PIR.not_isTPrivate_succ_shamirCube,
    Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_of_le_mul_self,
    Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_of_le_pow,
    Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_rows_of_le_pow,
    Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_prime_of_le_pow,
    Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_prime_rows_of_le_pow
  ]
  scope := "Because CGKS §1.1 (pp. 1–2) omits the polynomial construction details, PIR.Shamir \
    gives an explicit finite-field adaptation over Shamir.Params F S (|F| > |S|, instantiated \
    over ZMod p for primes p > k): linear Shamir PIR with matrix balancing gives \
    |S| * 2 m * ⌈log₂ |F|⌉ bits for n ≤ m², unbalanced degree-d hypercube PIR gives \
    |S| * ((d * ℓ + 1) * ⌈log₂ |F|⌉) bits for d * t < |S| and n ≤ ℓ^d, and applying §3.4's \
    rows balancing step (p. 11) gives |S| * ((d + 1) * ℓ * ⌈log₂ |F|⌉) bits for n ≤ ℓ^(d + 1). \
    At d = c - 1 (c ≥ 2, t ≥ 1), this is a weaker finite-field communication variant of CGKS \
    §1.1's headline claim: it matches the exact server count k = c * t and fixed-t database \
    exponent n^(1/c), but retains the field bit-width factor ⌈log₂ |F|⌉ (with |F| > c * t) \
    rather than proving §1.1's varying-t(n) O(t(n) * n^(1/c)) bound. Machine runtime (CGKS \
    §2.4, p. 6) and fair-coin realization of finite-uniform ProbComp sampling are not certified. \
    Any t + 1 colluding servers break privacy whenever |ι| ≥ 2 (for shamir) and whenever D is \
    nonempty (d ≥ 1) and |ι| ≥ 2 (for shamirCube; at empty D, D → ι is a singleton so privacy \
    holds trivially)."

register_result "cgks-pir-block-retrieval" where
  title := "Chor–Goldreich–Kushilevitz–Sudan: private block retrieval transformations and \
    constant-overhead schemes"
  topic := "cryptography"
  sources := [
    { paper := ChorGoldreichKushilevitzSudan1998,
      theorem := "Propositions 4–5 and Corollaries 6–8",
      locator := "Section 4 (pp. 11–13 of the April 21, 1998 journal version)" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PIR.Scheme.card_mul_le_communication_of_card_le,
    Cslib.Crypto.Protocols.PIR.Scheme.card_mul_le_communication,
    Cslib.Crypto.Protocols.PIR.hasBlockScheme_one_iff,
    Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect.toBlock,
    Cslib.Crypto.Protocols.PIR.Scheme.IsTPrivate.toBlock,
    Cslib.Crypto.Protocols.PIR.communication_toBlock_le,
    Cslib.Crypto.Protocols.PIR.communication_toBlock_of_card_answer,
    Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect.mapAnswerHom,
    Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect.sumChunks,
    Cslib.Crypto.Protocols.PIR.Scheme.IsTPrivate.sumChunks,
    Cslib.Crypto.Protocols.PIR.hasBlockScheme_of_xorReconstruct,
    Cslib.Crypto.Protocols.PIR.hasTPrivateBlockScheme_of_xorReconstruct,
    Cslib.Crypto.Protocols.PIR.hasBlockScheme_two_of_le,
    Cslib.Crypto.Protocols.PIR.hasBlockScheme_four_of_le_sq,
    Cslib.Crypto.Protocols.PIR.hasBlockScheme_four_of_le_half_sq
  ]
  scope := "One-round private retrieval of ℓ-bit blocks (Scheme ι S R Q A (κ → Bool)) from n \
    blocks with fixed-length binary encoding communication |S| * (⌈log₂ |Q|⌉ + ⌈log₂ |A|⌉) \
    (machine runtime in CGKS §2.4 is not modeled). Single-server (and full-coalition |S| ≤ t) \
    block retrieval requires at least n * ℓ bits (attained at k = 1 by PIR.download). \
    Proposition 4 (Scheme.toBlock) lifts any scheme by repeating answers across block \
    coordinates; Proposition 5 (Scheme.sumChunks) and its AddCommGroup homomorphism reduction \
    (Scheme.mapAnswerHom) compress m parallel XOR-reconstructed instances on Option ι into 1-bit \
    server answers, preserving t-privacy without finiteness assumptions on R or Q. Composing \
    them gives Corollary 6; specializing Proposition 4 to twoServer and cube (Fin 2) gives 4 * ℓ \
    bits with 2 servers for n ≤ ℓ (Corollary 7) and 8 * ℓ bits with 4 servers when n ≤ m² and \
    2 * m ≤ ℓ, in particular n ≤ (ℓ / 2)^2 (Corollary 8, replacing the paper's unrounded \
    n ≤ ℓ² / 4 with the integer subcube condition 2 * m ≤ ℓ, matching n ≤ ℓ² / 4 when ℓ is \
    even)."

register_result "cgks-pir-indexed-schemes" where
  title := "Chor–Goldreich–Kushilevitz–Sudan: PIR with per-server query and answer widths"
  topic := "cryptography"
  sources := [
    { paper := ChorGoldreichKushilevitzSudan1998,
      theorem := "Definition 1",
      locator := "Sections 2.1, 2.2, 3.3 (Footnote 1), and 5.1 (pp. 4–5, 9, 14 of the \
        April 21, 1998 journal version)" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PIR.indexedCommunication_const,
    Cslib.Crypto.Protocols.PIR.IndexedScheme.isTPrivate_one_iff,
    Cslib.Crypto.Protocols.PIR.IndexedScheme.isTPrivate_iff_tuple,
    Cslib.Crypto.Protocols.PIR.IndexedScheme.exists_injective_answers_of_card_le,
    Cslib.Crypto.Protocols.PIR.IndexedScheme.card_le_indexedCommunication_of_card_le,
    Cslib.Crypto.Protocols.PIR.HasTPrivateIndexedScheme.card_le_of_le,
    Cslib.Crypto.Protocols.PIR.hasIndexedScheme_one_iff
  ]
  scope := "One-round PIR schemes with server-indexed query and answer alphabets Q, A : S → Type \
    and per-server fixed-length binary encoding cost ∑ s, (⌈log₂ |Q s|⌉ + ⌈log₂ |A s|⌉) \
    (execution-dependent variable-length codes within a single server and §2.4 machine runtime \
    are not modeled). Embedding into uniform PIR.Scheme over Σ s, Q s and Σ s, A s \
    (IndexedScheme.toSigmaScheme) transfers coalition-privacy equivalences and the full-coalition \
    (|S| ≤ t) and single-server n-bit lower bounds without re-proving them."

register_result "cgks-pir-general-covering" where
  title := "Chor–Goldreich–Kushilevitz–Sudan: unbalanced covering-code PIR (Theorem 1) and \
    radius-r covering schemes"
  topic := "cryptography"
  sources := [
    { paper := ChorGoldreichKushilevitzSudan1998,
      theorem := "Theorem 1",
      locator := "Section 3.3, Footnote 1, Figure 1 (d = 5, k = 7), and p. 10 remark \
        (pp. 9–10 of the April 21, 1998 journal version)" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PIR.ExactRadiusOneCover.isCorrect_indexedScheme,
    Cslib.Crypto.Protocols.PIR.ExactRadiusOneCover.isPrivate_indexedScheme,
    Cslib.Crypto.Protocols.PIR.ExactRadiusOneCover.indexedCommunication_indexedScheme_eq,
    Cslib.Crypto.Protocols.PIR.ExactRadiusOneCover.hasIndexedScheme,
    Cslib.Crypto.Protocols.PIR.hasIndexedScheme_of_hammingDist,
    Cslib.Crypto.Protocols.PIR.hasIndexedScheme_seven_of_le_pow_five,
    Cslib.Crypto.Protocols.PIR.isCorrect_radiusCoverScheme,
    Cslib.Crypto.Protocols.PIR.isPrivate_radiusCoverScheme,
    Cslib.Crypto.Protocols.PIR.hasScheme_of_hammingDist_le,
    Cslib.Crypto.Protocols.PIR.hasScheme_of_hammingDist_two,
    Cslib.Crypto.Protocols.PIR.hasScheme_of_hammingDist_two_sq,
    Cslib.Crypto.Protocols.PIR.hasScheme_two_radius_two_of_le_pow_five
  ]
  scope := "Removes the balancedness hypothesis k * (m + 1) = 2^d from CGKS §3.3 Theorem 1 via \
    PIR.IndexedScheme: any injective radius-1 covering code c : S → D → Bool on nonempty D \
    (0 < |D|, made explicit because d - 1 truncates at d = 0 in ℕ and duplicate codewords would \
    violate |S| ≤ 2^d) gives k + (2^d + (d - 1) * k) * ℓ bits for n ≤ ℓ^d, instantiated on the \
    unbalanced optimal 7-word cover of {0, 1}^5 (60 * ℓ + 7 bits, matching Figure 1's 60 n^(1/5) \
    asymptotic term plus k). For general radius-r covers, radiusCoverScheme achieves \
    k * (d * ℓ + ∑_{j ≤ r} C(d, j) * ℓ^j) bits in uniform PIR.Scheme, specializing at r = 2 to \
    k * (2 d ℓ + C(d, 2) ℓ² + 1) (CGKS p. 10's displayed leading expression k d ℓ + k C(d, 2) ℓ² \
    plus the k * (d ℓ + 1) distance-0/1 answer bits; the literal k d ℓ + k C(d, 2) ℓ² bound \
    without lower-order answer terms is not proved) and the coarser polynomial upper bound \
    k * d * ℓ + k * d² * ℓ² (when 2 ≤ d and 1 ≤ ℓ). Server and user runtime (Remark on p. 10) is \
    not modeled."

register_result "cgks-pir-interactive-lower-bound" where
  title := "Chor–Goldreich–Kushilevitz–Sudan: interactive single-server PIR and block lower bounds"
  topic := "cryptography"
  sources := [
    { paper := ChorGoldreichKushilevitzSudan1998,
      theorem := unverified,
      locator := "Sections 4 and 5.1 (pp. 11–14 of the April 21, 1998 journal version)" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PIR.InteractiveScheme.injective_leaf,
    Cslib.Crypto.Protocols.PIR.InteractiveScheme.card_pow_card_le_ncard_transcripts,
    Cslib.Crypto.Protocols.PIR.InteractiveScheme.card_pow_card_le_leafCount,
    Cslib.Crypto.Protocols.PIR.InteractiveScheme.card_le_depth,
    Cslib.Crypto.Protocols.PIR.InteractiveScheme.card_mul_le_depth,
    Cslib.Crypto.Protocols.PIR.InteractiveScheme.exists_iff,
    Cslib.Crypto.Protocols.PIR.InteractiveScheme.exists_block_iff
  ]
  scope := "Arbitrary-round deterministic protocol trees (Communication.Protocol) with \
    independent ProbComp userCoins i and serverCoins over general payload β (defaulting to Bool). \
    Replaces CGKS §5.1's deterministic-output step with Protocol.leaf_eq_iff (rectangle \
    property), forcing |β|^|ι| leaves, |ι| bits on Boolean databases, and |ι| * |κ| bits on \
    (κ → Bool) block databases (attained by download and blockDownload)."

register_result "cgks-pir-multi-interactive-lower-bound" where
  title := "Chor–Goldreich–Kushilevitz–Sudan: multi-server interactive PIR and full-coalition \
    lower bounds"
  topic := "cryptography"
  sources := [
    { paper := ChorGoldreichKushilevitzSudan1998,
      theorem := unverified,
      locator := "Sections 2.1, 2.2, 4, and 5.1 (pp. 4–5, 11–14 of the April 21, 1998 journal \
        version)" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PIR.MultiRoundTree.depth_compile,
    Cslib.Crypto.Protocols.PIR.MultiInteractiveScheme.isTPrivate_one_iff,
    Cslib.Crypto.Protocols.PIR.MultiInteractiveScheme.isPrivate_toInteractiveScheme_of_card_le,
    Cslib.Crypto.Protocols.PIR.MultiInteractiveScheme.card_le_depth_of_card_le,
    Cslib.Crypto.Protocols.PIR.MultiInteractiveScheme.card_mul_le_depth_of_card_le
  ]
  scope := "Channel-isolated adaptive multi-round k-server PIR (MultiInteractiveScheme), where \
    each step exchanges 1 bit between the user and a chosen server s and serverBit s depends only \
    on x, d s, and the directional ChannelMsg history previously exchanged on s's channel (and \
    IsPrivate / IsTPrivate compare communication sub-traces rather than full server views). \
    Compiling to two-party InteractiveScheme preserves worst-case tree depth and transfers the \
    |ι|-bit and |ι| * |κ|-bit lower bounds whenever all servers may collude (|S| ≤ t). \
    Multi-round lower bounds below full collusion (t < |S|) are not proved."

register_result "generic-access-structure-secret-sharing" where
  title := "In the generic secret-sharing construction, every authorized coalition reconstructs \
    the secret and, over a finite group with uniform pads, every unauthorized coalition sees a \
    uniform view, when the empty coalition is unauthorized"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Construction 22.1: correctness and the secret-independence of unauthorized \
        views, with a correction",
      locator := "Section 22.5.1, p. 977; Definitions 22.17–22.20, pp. 975–976" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.SecretSharing.genericReconstruct_genericShare,
    Cslib.Crypto.Protocols.SecretSharing.genericUniform_viewDist_eq
  ]
  scope := "Parties form any finite type with decidable equality (the book: {1, …, N}), the \
    access structure is any monotone family A of coalitions (Definitions 22.17–22.18), and \
    secrets lie in an additive commutative group G (the book: Z_q). genericShare is \
    Construction 22.1: for each authorized J ∈ A it makes an independent |J|-out-of-|J| \
    additive sharing of the secret from |J| − 1 pads of the key, and party i holds one element \
    for each J ∈ A^(i) = {J ∈ A : i ∈ J}. genericReconstruct sums the J-coordinates of the \
    members of J. genericReconstruct_genericShare: every authorized coalition reconstructs the \
    secret, for every key (the correctness condition of Definition 22.19). \
    genericUniform_viewDist_eq: for finite G and uniform pads, the view of every unauthorized \
    coalition is uniform, so its law does not depend on the secret (the condition of \
    Definition 22.20). Definition 22.19 also asks for efficient sharing and combining \
    algorithms; the model is information-theoretic and claims no running time, so the entry \
    does not say that the construction implements the access structure in that sense. \
    Reconstruction is total, returning 0 on unauthorized coalitions. Correction: both theorems \
    assume that ∅ is not authorized. Definition 22.18 allows ∅ ∈ A, but then the empty \
    coalition's view, which carries no information, would have to determine the secret: no \
    scheme over a secret space with at least two elements and a nonempty key space is correct \
    (not_perfectlyCorrect_of_authorized_empty, in AccessStructure/Recognition.lean; a key \
    space carrying a key distribution is nonempty). The smaller shares of Example 22.1, which \
    shares only over minimal authorized sets, are not formalized."

open Cslib.Crypto.Protocols.SecretSharing in
register_result "access-structure-recognition-test" where
  title := "The recognition test of a secret-sharing scheme accepts authorized coalitions with \
    probability 1 and unauthorized ones with probability 1/|Z|"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "recognizing authorized coalitions with a secret-sharing scheme (unnumbered): \
        the acceptance probabilities",
      locator := "Section 22.5, p. 976" }
  ]
  theorems := [
    AccessScheme.recognizeCoalitionDist_eq_pure_true_of_authorized,
    AccessScheme.recognizeCoalitionDist_true_of_not_authorized,
    AccessScheme.recognizeCoalitionDist_true_eq_one_iff
  ]
  scope := "For any AccessScheme over a finite nonempty secret space Z: shares are computed from \
    a key drawn from a key distribution P, every authorized coalition reconstructs the secret \
    for every key, and every unauthorized coalition's view has the same law for all secrets \
    under every allowed P (Definitions 22.19–22.20, pp. 975–976, without running times). \
    recognizeCoalitionDist is the book's test on a coalition J: draw α uniformly from Z, share \
    it, reconstruct on J and accept when the result is α. It accepts with probability 1 on every \
    authorized J, for every key distribution \
    (recognizeCoalitionDist_eq_pure_true_of_authorized), and with probability exactly 1/|Z| on \
    every unauthorized J under an allowed P (recognizeCoalitionDist_true_of_not_authorized). \
    For |Z| ≥ 2, acceptance with probability 1 holds exactly for the authorized coalitions \
    (recognizeCoalitionDist_true_eq_one_iff). The book concludes that A is efficiently \
    recognizable; this entry states only the acceptance probabilities, and AccessScheme has no \
    cost model, so no efficiency is claimed. The book's combiner is defined on authorized \
    coalitions only, while its test runs it on any J; here reconstruction is total."

register_result "beaver-multiplication-gate-honest-but-curious" where
  title := "Beaver's multiplication gate with dealer triples, for m ≥ 1 parties, outputs shares \
    of the product and gives exact joint simulation of the corrupted views and all outputs for \
    every proper static coalition (simulator without an efficiency certificate)"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "the multiplication-gate protocol of Figure 23.3: output correctness, and its \
        honest-but-curious privacy (unnumbered) as exact joint simulation of the corrupted views \
        and all outputs",
      locator := "Section 23.2.2, pp. 1007–1009" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.MPC.Beaver.sum_output_beaverMulProtocol,
    Cslib.Crypto.Protocols.MPC.Beaver.perfectSemiHonestPrivateProper_beaverMul
  ]
  scope := "Over ZMod p for any p > 0 (the book: a prime q) and for any number m ≥ 1 of parties \
    (the book: two, P₁ and P₂, with a dealer); the correctness theorem assumes m ≥ 1, and for \
    m = 0 there is no proper coalition. The dealer functionality beaverTripleFunctionality \
    gives party i the triple share (a_i, b_i, c_i), where a and b are uniform share vectors and \
    c is a uniform additive sharing of (Σa)(Σb); for m = 2 this is the book's Beaver triple \
    sharing (p. 1007). beaverMulProtocol is Figure 23.3 for m parties: each party broadcasts \
    (x_i − a_i, y_i − b_i), all parties sum the openings to (u, v), and party i outputs \
    [i = 0]·uv + u·b_i + v·a_i + c_i. sum_output_beaverMulProtocol: on every execution the \
    output shares sum to (Σx)(Σy). perfectSemiHonestPrivateProper_beaverMul: for every proper \
    static coalition I (any set of parties other than all of them) and all inputs, the joint \
    law of I's views and all parties' outputs equals the law obtained by drawing the outputs \
    from the ideal functionality sharedMulFunctionality (a fresh uniform additive sharing of \
    (Σx)(Σy)) and the views from the explicit simulator beaverMulSim, given I's inputs and \
    outputs. The equality is exact, so it holds against unbounded distinguishers, as in the \
    book's remark that honest-but-curious security is unconditional (p. 1009). The simulator \
    has no efficiency certificate, so no efficient simulation is claimed. The dealer is the \
    ideal triple functionality, as in the book. Only one multiplication gate is formalized: \
    input sharing, the other gates, output opening and the whole circuit protocol of \
    Section 23.2.3 are not. The tampered-opening game in the same module \
    (le_advantage_tamperedOpeningBitGame) is the module's own illustration, motivated by \
    Section 23.2.4, and is not part of this entry."

register_result "oprf-dh-blinding-laws" where
  title := "Protocols OPRF1 and OPRF2: group-element correctness and the blinding laws of the \
    receiver's message and of a deviating sender's error, with two corrections"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Protocols OPRF1 and OPRF2 (unnumbered): correctness on group elements, what \
        the sender sees, and the effect of a wrong answer, with two corrections",
      locator := "Section 11.6.3, pp. 454–456" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.OPRF.maskedUnblind_smul_maskedBlind,
    Cslib.Crypto.Protocols.OPRF.maskedUnblind_smul_maskedBlind_add,
    Cslib.Crypto.Protocols.OPRF.uniformOfFintype_bind_maskedBlind,
    Cslib.Crypto.Protocols.OPRF.uniformOfFintype_bind_maskedUnblind_add_of_ne_zero,
    Cslib.Crypto.Protocols.OPRF.uniformOfFintype_bind_units_smul_of_ne_zero
  ]
  scope := "The group G is written additively as a ZMod q-module with a generator g (every \
    element is c • g), the hashed input H(x) is a fixed element h of G, and ρ is uniform on the \
    units of ZMod q, which for prime q are the book's nonzero exponents. OPRF2 (p. 456): \
    maskedBlind g ρ τ h = ρ • h + τ • g is v = H(x)^ρ · g^τ, and \
    maskedUnblind u ρ τ w = ρ⁻¹ • (w − τ • u) is (w/u^τ)^(1/ρ). The first two theorems are \
    identities of group elements. maskedUnblind_smul_maskedBlind: with u = k • g and the honest \
    reply w = k • v, the receiver obtains k • h = H(x)^k. At τ = 0 the message is ρ • h and the \
    unblinding is ρ⁻¹ • w, so this identity is also OPRF1's correctness (pp. 454–455). \
    maskedUnblind_smul_maskedBlind_add: a reply k • v + d gives k • h + ρ⁻¹ • d, the book's \
    H(x)^k · d^(1/ρ). The other three theorems are exact equalities of distributions, through \
    an arbitrary continuation, so they hold against unbounded observers. \
    uniformOfFintype_bind_maskedBlind: for every h and every ρ, v has the law of τ • g under \
    uniform τ, so it reveals nothing about x or ρ. \
    uniformOfFintype_bind_maskedUnblind_add_of_ne_zero (q prime): against a sender who answers \
    v with k • v + d(v), d(v) ≠ 0 for every v, the pair of v and the unblinded value has the law \
    of (τ • g, k • h + ρ • g) for independent uniform τ and ρ. Correction 1: the error term \
    ρ⁻¹ • d(v) is never 0, so it is not uniform over G as p. 456 says. \
    uniformOfFintype_bind_units_smul_of_ne_zero (q prime), for OPRF1: for h ≠ 0, ρ • h has the \
    law of ρ • g. Correction 2: for a fixed public hash function H, the law of the OPRF1 message \
    v = H(x)^ρ is the same for all inputs x with H(x) ≠ 1, but an input with H(x) = 1 always \
    gives v = 1, so the book's claim that v is independent of x needs H(x) ≠ 1 (for a random \
    oracle H, H(x) = 1 has probability 1/q). Outside the registered statements: the \
    interactive executions, the final hash y = H′(x, ·) and the function F′ of (11.21), that a \
    wrong OPRF2 output is uniform in Y, Exercise 11.3, and security against a malicious \
    receiver under the one-more Diffie–Hellman assumption."

register_result "sigma-composition-efficient-extraction" where
  title := "Polynomial-time special-soundness extraction under Sigma-protocol composition"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Theorem 19.18 (special soundness); Theorem 19.19 (special soundness); \
        Exercise 19.6(b)",
      locator := "Theorem 19.18: Version 0.6, Section 19.7.1, pp. 787–788; \
        Theorem 19.19: Version 0.6, Section 19.7.2, p. 789; \
        Exercise 19.6(b): Version 0.6, pp. 810–811" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.SigmaProtocol.EfficientSpecialSoundness.andProof,
    Cslib.Crypto.Protocols.SigmaProtocol.EfficientSpecialSoundness.orProof,
    Cslib.Crypto.Protocols.SigmaProtocol.EfficientSpecialSoundness.parallelRepetition
  ]
  scope := "Preservation of polynomial-time extraction for AND, OR and positive k-fold parallel \
    repetition, from the component extractors' correctness and efficiency certificates. The \
    composed extractors are constructed and certified; no efficiency of a constructed extractor \
    is assumed. Relations and encodings are explicit, witness types may differ, and OR uses a \
    finite additive group with polynomial-time encoded challenge subtraction, generalizing the \
    source's bit-string XOR group. Equal parallel challenge tuples use the component extractor \
    at coordinate zero, with no efficient-default premise. The separate zero-fold extension is \
    not this source result. These entries concern extraction preservation; honest-prover and \
    verifier efficiency are separate properties."

register_result "sigma-composition-exact-efficient-simulation" where
  title := "Exact strict-PPT special-HVZK simulation under Sigma-protocol composition"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Theorem 19.18 (special HVZK); Theorem 19.19 (special HVZK); Exercise 19.6(c)",
      locator := "Theorem 19.18: Version 0.6, Section 19.7.1, pp. 787–788; \
        Theorem 19.19: Version 0.6, Section 19.7.2, p. 789; \
        Exercise 19.6(c): Version 0.6, pp. 810–811" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.SigmaProtocol.EfficientSpecialHVZK.andProof,
    Cslib.Crypto.Protocols.SigmaProtocol.EfficientSpecialHVZK.orProof,
    Cslib.Crypto.Protocols.SigmaProtocol.EfficientSpecialHVZK.parallelRepetition
  ]
  scope := "The cited exact simulation preservation results are the zero-error specializations \
    of these quantitative theorems: component errors and the OR challenge-sampling error are \
    all zero, so the constructed simulator's error is zero. Simulator programs and uniform \
    strict-PPT certificates are constructed from the components' certificates, with the same \
    composed protocols used in their exact transcript laws. OR uses a finite additive group \
    with certified challenge subtraction and an exact strict-PPT uniform sampler, including \
    the source's XOR challenge space. General nonzero-error bounds remain quantitative API, \
    not claims of exact special HVZK. Source repetition has k ≥ 1; the library also permits \
    k = 0. Honest-prover and verifier efficiency are separate properties."

register_result "sigma-language-reduction-correctness-hvzk" where
  title := "A language reduction transfers correctness and the special-HVZK simulation laws of a \
    Sigma protocol to the reduced relation"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "language reductions, conditions (i)–(ii): inheritance of correctness and \
        special HVZK (unnumbered)",
      locator := "Section 20.2, p. 829; Definitions 19.3 and 19.5, pp. 772 and 774" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.SigmaProtocol.LanguageReduction.complete,
    Cslib.Crypto.Protocols.SigmaProtocol.LanguageReduction.specialHVZK
  ]
  scope := "LanguageReduction R R′ f g is the book's pair of maps f : X × Y → X′ (curried here) \
    and g : Y → Y′ with (i) (f(x, y), g(y)) ∈ R′ for every (x, y) ∈ R and (ii) g(y) ∈ L_R′ \
    implies y ∈ L_R, for typed relations; unlike the book, it does not require f and g to be \
    efficiently computable. The derived protocol P′.comap f g runs the prover of P′ on \
    (f(x, y), g(y)) and its verifier on g(y), with the same commitments, challenges and \
    responses. LanguageReduction.complete: if P′ is complete for R′ (every honest conversation \
    is accepting, for every challenge, the requirement of Definition 19.3), the derived protocol \
    is complete for R. LanguageReduction.specialHVZK: if P′ is special HVZK for R′ with \
    simulator Sim′, the derived protocol is special HVZK for R with the simulator \
    (y, c) ↦ Sim′(g(y), c). Both use only condition (i). The typed SpecialHVZK has both clauses \
    of Definition 19.5 (simulated conversations accept for every statement and challenge, and \
    for (x, y) ∈ R the simulation at each fixed challenge has the honest transcript law) but \
    does not require an efficient simulator; the efficient form is the entry \
    sigma-language-reduction-efficient-transfer, and soundness is the entry \
    sigma-language-reduction-soundness. The book's remark that knowledge soundness need not be \
    inherited corresponds to SpecialSoundness.comap and SpecialSoundness.mapWitness, which are \
    not listed."

register_result "sigma-language-reduction-soundness" where
  title := "A language reduction transfers statistical soundness of a Sigma protocol, and from \
    special soundness gives soundness error at most 1/|C| against every prover"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "language reductions: inheritance of soundness (unnumbered), in its statistical \
        form, with Theorem 20.1",
      locator := "Section 20.2, p. 829; Theorem 20.1 and Remark 20.1, Section 20.1, p. 824" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.SigmaProtocol.LanguageReduction.sound,
    Cslib.Crypto.Protocols.SigmaProtocol.sound_comap
  ]
  scope := "Soundness is statistical soundness, Verifier.Sound World.plain (language R) langOut ε: \
    for every false statement y (one with no witness) and every prover strategy, unbounded in \
    time and randomness, the verifier accepts with probability at most ε (langOut is all \
    outputs by default). This is Attack Game 20.1 (p. 824) with the false statement fixed in \
    advance; as the bound holds for every false statement and every prover, it also bounds a \
    prover that chooses y* first, and it is statistical soundness in the sense of Remark 20.1. \
    sound_comap: if the verifier of P′ is statistically sound for L_R′ with error at most ε, \
    the derived verifier (that of P′ run on g(y)) is statistically sound for L_R with error at \
    most ε; it uses only condition (ii) and nothing about f. LanguageReduction.sound: if P′ has \
    special soundness (Definition 19.4 without the efficiency of the extractor, which soundness \
    does not use) and the challenge space C is finite and nonempty, the derived protocol is \
    statistically sound with error at most 1/|C|, which is Theorem 20.1 for P′ carried through \
    the reduction. Computational soundness (Definition 20.2) follows when |C| is super-poly; \
    the transfer of computational soundness from a P′ that is only computationally sound is not \
    formalized. Language reductions and the derived protocol are as in the entry \
    sigma-language-reduction-correctness-hvzk."

register_result "sigma-language-reduction-efficient-transfer" where
  title := "A polynomial-time statement map transfers efficient special-HVZK simulation and \
    efficient verification along a language reduction"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "language reductions: inheritance of special HVZK (unnumbered), with efficient \
        simulators",
      locator := "Section 20.2, p. 829; Definition 19.5, p. 774" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.SigmaProtocol.EfficientSpecialHVZK.comap,
    Cslib.Crypto.Protocols.SigmaProtocol.EfficientVerifier.comap
  ]
  scope := "For an indexed family P′ i of Sigma protocols with word encodings of index, \
    statements, commitments, challenges and responses, and a statement map g i whose word form \
    gw is computable in polynomial time and agrees with g on encodings; the derived family \
    (P′ i).comap (f i) (g i) is encoded with a new statement encoding. \
    EfficientSpecialHVZK.comap: under condition (i) of the language reduction, if P′ is special \
    HVZK with a typed simulator family satisfying both clauses of Definition 19.5 exactly, which \
    one uniform strict PPT program realizes up to statistical distance δ i \
    (EfficientSpecialHVZK), then so is the derived family, with the same δ: the derived \
    simulator computes g and runs the simulator of P′, and its certificate is built from that \
    of P′. The instance δ = 0 is the one in which the efficient simulator itself satisfies \
    Definition 19.5's exact laws; a positive δ bounds the program's distance from the exact \
    simulator, such as an implementation's sampling error. EfficientVerifier.comap: the \
    derived verifier's deterministic acceptance test on a transcript (statement, commitment, \
    challenge, response), which computes g and runs that of P′, is computable in polynomial time \
    when that of P′ is; the certificate covers this test only and supplies no challenge \
    sampler. The witness map f need not be efficient, and the efficiency of the derived honest \
    prover is not formalized, since the library has no efficiency predicate for honest \
    Sigma-protocol provers. EfficientSpecialSoundness.comap and \
    EfficientSpecialSoundness.mapWitness, in the same module, concern the extraction of a \
    witness for g(y) and its mapping back, that is, knowledge soundness, which the book says \
    need not be inherited; they are not listed."

register_result "sigma-unique-responses-strong-special-soundness" where
  title := "Schnorr's and Chaum–Pedersen's Sigma protocols have unique responses, the generic \
    linear protocol has them exactly when its homogeneous system has only the zero solution, \
    and unique responses with special soundness give strong special soundness"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercises 19.14(a)–(c) and 19.15(a)",
      locator := "Section 19.12, pp. 813–814" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.SigmaProtocol.SpecialSoundness.strong,
    Cslib.Crypto.Protocols.SigmaProtocol.schnorr_uniqueResponses,
    Cslib.Crypto.Protocols.SigmaProtocol.chaumPedersen_uniqueResponses,
    Cslib.Crypto.Protocols.SigmaProtocol.linearSystem_uniqueResponsesAt_iff
  ]
  scope := "UniqueResponses is the definition of Exercise 19.14: two accepting conversations \
    (t, c, z) and (t, c, z′) for a statement have z = z′. StrongSpecialSoundness is that of \
    Exercise 19.15: the extractor returns a witness from accepting (t, c, z) and (t, c′, z′) \
    whenever (c, z) ≠ (c′, z′). SpecialSoundness.strong (19.15(a)): special soundness and \
    unique responses give strong special soundness with the same extractor, so an efficiency \
    certificate for that extractor serves unchanged (the typed predicates themselves do not \
    require efficiency). The protocols are over an additive ZMod q-module G, with challenges \
    embedded in Z_q. schnorr_uniqueResponses (19.14(a)) and chaumPedersen_uniqueResponses \
    (19.14(b), at every statement, Diffie–Hellman triple or not) assume that r ↦ r • g is \
    injective, which holds for the generator g of the book's groups of prime order q, so in the \
    book's setting these hold without further condition. linearSystem_uniqueResponsesAt_iff \
    (19.14(c)): for a nonempty challenge set, the generic linear protocol (Figure 19.8 on \
    formulas (19.13)) has unique responses at a system exactly when its homogenized system has \
    only the zero solution. Without that condition it does not have them: over Z_2, a single \
    equation whose coefficient is the identity accepts both responses 0 and 1. The exercise \
    asks for the 'if' direction, and prints the unique solution as α_j = 1; the trivial \
    solution, in which every exponent α_j is 0, is what the theorem states. \
    schnorr_strongSpecialSoundness, in the same module, combines 19.14(a) and 19.15(a) for prime \
    q and g ≠ 0. Exercises 19.14(d), 19.15(b) and 19.16 are not formalized."

register_result "chaum-pedersen-sigma-protocol" where
  title := "The Chaum–Pedersen Sigma protocol for Diffie–Hellman triples is complete and \
    efficiently special sound, with 2/2^n statistical closeness and computational special HVZK"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 19.10",
      locator := "Section 19.5.2, pp. 777–778 (with Figure 19.7 and (19.12)); Definitions \
        19.3–19.5, Section 19.4, pp. 772–774; Attack Game 20.4 and Definition 20.6, \
        Section 20.4.2, p. 840" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.chaumPedersenProbFamily_complete,
    Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialSoundness_chaumPedersenProb,
    Cslib.Crypto.PrimeOrderGroupFamily.closeTo_transcript_chaumPedersenProbFamily_simulator,
    Cslib.Crypto.PrimeOrderGroupFamily.advantage_chvzkGame_chaumPedersenProbFamily_le,
    Cslib.Crypto.PrimeOrderGroupFamily.computationalSpecialHVZK_chaumPedersen
  ]
  scope := "Over any PrimeOrderGroupFamily F at index i = (n, d) with prime order q = F.order d, \
    statement (u, v, w) : F.Carrier d × F.Carrier d × F.Carrier d, witness β : ZMod q for the \
    Diffie–Hellman triple relation β • g = v ∧ β • u = w ((19.12), written additively), and \
    challenges in ZMod q, encoded by chaumPedersenEncoding (framed element tuples and binary \
    scalars). In F.chaumPedersenProbFamily i (Figure 19.7, p. 777), the honest prover samples its \
    commitment nonce with F.sampleExp n d (chaumPedersenCommit, certified uniform strict PPT on \
    encodings by chaumPedersenCommitWord, eval_chaumPedersenCommitWord and \
    isPPTOn_chaumPedersenCommitWord) and computes r + c * β (certified deterministic polynomial \
    time on encodings by schnorrRespondBits, computableInPolyTime_schnorrRespondBits and \
    schnorrRespondBits_chaumPedersen), while the verifier checks z • g = t₁ + c • v and \
    z • u = t₂ + c • w (certified deterministic polynomial time in \
    CslibFrontier.Crypto.Computational.ChaumPedersenProtocol.Verifier by \
    efficientVerifier_chaumPedersenProb). \
    chaumPedersenProbFamily_complete proves completeness (Definition 19.3). \
    efficientSpecialSoundness_chaumPedersenProb proves efficient special soundness \
    (Definition 19.4) via chaumPedersenExtract and schnorrExtractWord. The simulator \
    chaumPedersenSimulator samples z with F.sampleExp n d and outputs \
    ((z • g − c • v, z • u − c • w), z), certified uniform strict PPT by \
    chaumPedersenSimulateWord (isPPT_chaumPedersenSimulator) and outputting an accepting \
    conversation with probability 1 on every statement and challenge \
    (accepts_chaumPedersenSimulator, Definition 19.5(i)). On every valid witness-statement pair \
    and challenge c, closeTo_transcript_chaumPedersenProbFamily_simulator bounds the statistical \
    distance between honest and simulated transcripts by 2/2^n (1/2^n from each sampleExp draw); \
    advantage_chvzkGame_chaumPedersenProbFamily_le bounds Attack Game 20.4 advantage by 2/2^n \
    against arbitrary (even computationally unbounded) two-stage adversaries; and \
    computationalSpecialHVZK_chaumPedersen establishes Definition 20.6 with exact zero acceptance \
    error (δ = fun _ => 0) along (setup n).map (n, ·) against all uniform strict PPT \
    CHVZKAdversary families (with no computational hardness assumption). Deviations: (1) in the \
    uniform strict-PPT fair-coin model, neither the prover nor the simulator can sample ZMod q \
    with zero error when q is not a power of two (unlike Definition 2.8, p. 30, which permits \
    negligible runtime-overflow probability and exact rejection sampling), so Definition 19.5(ii) \
    identical transcript distribution is relaxed to 2/2^n statistical closeness and Definition \
    20.6 ComputationalSpecialHVZK with exact Definition 19.5(i) acceptance; (2) the challenge \
    space is C = ZMod q (the 2/2^n transcript bound holds pointwise at every c : ZMod q and thus \
    for any subset C ⊆ ZMod q, while Attack Game 20.4 draws c uniformly from ZMod q); (3) groups \
    are written additively and setup : ℕ → PMF F.Desc is arbitrary."

register_result "prp-prf-switching" where
  title := "PRP/PRF switching lemma: PRP and PRF advantages differ by at most a birthday term"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorems 4.4 and 4.6",
      locator := "Section 4.4.3, pp. 134–135" }
  ]
  theorems := [
    Cslib.Crypto.PRP.advantage_idealExperiment_prfIdealExperiment_le,
    Cslib.Crypto.PRP.abs_advantage_sub_prfAdvantage_le,
    Cslib.Crypto.PRP.prfAdvantage_le_advantage_add
  ]
  scope := "Finite block set D and key set Key, block ciphers E : Key → Equiv.Perm D, and \
    adaptive oracle adversaries with private coins (PRF.Adversary D D) making at most Q queries \
    on every path (IsQueryBounded Q), with no bound on running time, as in the source. \
    Theorem 4.6 (advantage_idealExperiment_prfIdealExperiment_le): a uniform permutation and a \
    uniform function of D are distinguished with advantage at most Q.choose 2 / |D|. \
    Theorem 4.4 (abs_advantage_sub_prfAdvantage_le): the PRP and PRF advantages of E differ in \
    absolute value by at most Q.choose 2 / |D|; prfAdvantage_le_advantage_add is its PRP-to-PRF \
    half. The bound Q (Q - 1) / 2|D| is at most the source's Q² / 2N, so each statement implies \
    the source's. Concrete information-theoretic bounds; the asymptotic Corollary 4.5 is the \
    entry prp-iff-prf."

register_result "prp-iff-prf" where
  title := "A block cipher with a super-polynomial block space is a PRP iff it is a PRF"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Corollary 4.5", locator := "Section 4.4.3, p. 135" }
  ]
  theorems := [
    Cslib.Crypto.BlockCipher.prp_iff_indistinguishable_prpRealGame_prfIdealGame
  ]
  scope := "Every uniform block cipher (BlockCipher: polynomial-time key and block lengths, and \
    deterministic polynomial-time encryption and decryption, mutually inverse on blockLen n-bit \
    blocks under keyLen n-bit keys), with any key length, against uniform oracle-PPT \
    distinguishers (IsOraclePPT) in the adaptive word-oracle forms of Attack Games 4.1 and 4.2, \
    where a query of the wrong length is answered with the empty word in both games. The \
    source's super-poly N is the hypothesis that (2 ^ blockLen n)⁻¹ is negligible. The PRF side \
    is stated as indistinguishability of E.prpRealGame, which is the real experiment of E viewed \
    as a PRF over (K, X, X), from prfIdealGame blockLen blockLen; the library's named PRF notion \
    PseudorandomFunctionOver draws n-bit keys, and the keyLen = id case in that notion is \
    BlockCipher.prp_iff_pseudorandomFunctionOver_of_keyLen_eq_id, in the same module."

register_result "prp-birthday-distinguisher" where
  title := "A collision test on Q distinct queries has PRF advantage at least \
    min(Q(Q − 1)/4N, 0.63) against every block cipher, and at least 1/2 on all N ≥ 2 blocks"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "birthday distinguisher (unnumbered)",
      locator := "Section 4.4.3, p. 134" }
  ]
  theorems := [
    Cslib.Crypto.PRP.coe_advantage_birthdayDistinguisher,
    Cslib.Crypto.PRP.min_le_advantage_birthdayDistinguisher,
    Cslib.Crypto.PRP.half_le_advantage_birthdayDistinguisher_of_bijective
  ]
  scope := "A block cipher E : Key → Perm D over finite nonempty key and block sets, with \
    N = |D|, viewed as a PRF in the finite PRF experiment of Attack Game 4.2 with a uniform key \
    and a uniform random function. birthdayDistinguisher x queries the Q blocks of an injective \
    tuple x, so Q ≤ N, and outputs 1 iff two answers collide; against E it outputs 0 surely. \
    coe_advantage_birthdayDistinguisher: its advantage is exactly \
    1 − N(N − 1)⋯(N − Q + 1)/N^Q. min_le_advantage_birthdayDistinguisher: the advantage is at \
    least min(Q(Q − 1)/4N, 0.63). half_le_advantage_birthdayDistinguisher_of_bijective: when x \
    enumerates D and N ≥ 2, the advantage 1 − N!/N^N is at least 1/2; the book leaves N ≥ 2 \
    implicit, and at N = 1 the advantage is 0. Concrete and information-theoretic: the \
    distinguisher makes Q queries (isQueryBounded_birthdayDistinguisher) and no running time is \
    stated here. The polynomial-time distinguisher on bit strings is the entry \
    block-cipher-birthday-not-prf."

register_result "block-cipher-birthday-not-prf" where
  title := "A polynomial-time birthday distinguisher with q = min(Q(n), N) distinct queries has \
    PRF advantage at least min(q(q − 1)/4N, 0.63), so a block cipher with eventually positive \
    block length whose block space is not super-polynomial is not a PRF"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "birthday distinguisher and the argument for small N (unnumbered)",
      locator := "Section 4.4.3, p. 134" }
  ]
  theorems := [
    Cslib.Crypto.isOraclePPT_wordBirthdayDistinguisher,
    Cslib.Crypto.BlockCipher.min_le_prfAdvantage_wordBirthdayDistinguisher,
    Cslib.Crypto.BlockCipher.half_le_prfAdvantage_wordBirthdayDistinguisher,
    Cslib.Crypto.BlockCipher.not_indistinguishable_prpRealGame_prfIdealGame,
    Cslib.Crypto.BlockCipher.not_pseudorandomFunctionOver_of_not_negligible
  ]
  scope := "Every uniform block cipher (BlockCipher, as in the entry prp-iff-prf), with \
    N = 2^(blockLen n). wordBirthdayDistinguisher blockLen Q queries q = min(Q(n), N) distinct \
    blockLen n-bit words and outputs 1 iff two answers collide. \
    isOraclePPT_wordBirthdayDistinguisher: it is uniform oracle-PPT when blockLen and Q are \
    computable in polynomial time in unary, the book's poly-bounded Q. With n-bit keys \
    (keyLen = id, the keys of PseudorandomFunctionOver): \
    BlockCipher.min_le_prfAdvantage_wordBirthdayDistinguisher gives PRF advantage at least \
    min(q(q − 1)/4N, 0.63) at every n, and \
    BlockCipher.half_le_prfAdvantage_wordBirthdayDistinguisher gives at least 1/2 when N ≥ 2 \
    and Q(n) ≥ N, the book's 1 − N!/N^N ≥ 1/2. The cap q ≤ N matters: at N = 2 a budget of \
    Q(n) = 4 queries gives advantage exactly 1/2, below min(Q(Q − 1)/4N, 0.63) = 0.63. At \
    N = 1 a random permutation and a random function coincide, so the asymptotic statements \
    need positive block length. The book's 'N small' is read asymptotically as N not \
    super-poly, that is, 1/N not negligible. \
    BlockCipher.not_indistinguishable_prpRealGame_prfIdealGame: for any key length, if 1/N over \
    the n with nonzero block length is not negligible, a uniform oracle-PPT adversary \
    distinguishes E.prpRealGame from prfIdealGame. \
    BlockCipher.not_pseudorandomFunctionOver_of_not_negligible: with n-bit keys and block length \
    eventually at least 1, if 1/N is not negligible, E is not a PseudorandomFunctionOver. The PRF \
    games answer a query of the wrong length with the empty word; the distinguisher makes none. \
    The converse for super-poly N is Corollary 4.5, the entry prp-iff-prf."

register_result "brute-force-collision-search" where
  title := "Brute-force collision search finds a collision in 2^ℓ + 1 hash evaluations"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Section 8.3 brute-force collision search",
      locator := "Section 8.3, pp. 293–294" }
  ]
  theorems := [
    Cslib.Crypto.isQueryBounded_bruteForceHashFinder,
    Cslib.Crypto.bruteForceHashFinder_success,
    Cslib.Crypto.bruteForceFinder_two_pow_succ_success,
    Cslib.Crypto.isQueryBounded_bruteForceFinder,
    Cslib.Crypto.bruteForceFinder_success
  ]
  scope := "For any s distinct messages ms : Fin s → M and oracle program digest making at most \
    c external oracle calls per message, bruteForceFinder digest ms makes at most s·c oracle \
    calls on every path (isQueryBounded_bruteForceFinder) and, against any deterministic oracle \
    realizing f : M → T with digests in a finite set D of cardinality D.card < s, outputs a \
    collision in collisionOutputs f with probability 1 (bruteForceFinder_success); every \
    non-none output is a collision (bruteForceFinder_sound). Specializing to ℓ-bit digests \
    (D = BitString.wordsOfLength ℓ, of size 2^ℓ < 2^ℓ + 1) for any ℓ : ℕ gives probability-1 \
    collision finding on any 2^ℓ + 1 distinct messages (bruteForceFinder_two_pow_succ_success), \
    and bruteForceHashFinder ℓ queries a hash H : List Bool → List Bool once on each of the \
    first 2^ℓ + 1 binary words of length ℓ + 1 (BitString.lowBits (ℓ + 1)), finding a collision \
    with probability 1 whenever H maps (ℓ + 1)-bit words to ℓ-bit digests \
    (bruteForceHashFinder_success) in at most 2^ℓ + 1 hash evaluations \
    (isQueryBounded_bruteForceHashFinder). Deviations: (1) costs count external oracle calls \
    (ProbOracleComp.IsQueryBounded), not Turing-machine steps for message enumeration or \
    searching the 2^ℓ + 1 digests in collidingPair? (the polynomial-time Turing-machine \
    refutation of CollisionResistantOn when 2^ℓ(n) is polynomial in n is \
    not_collisionResistantOn_of_bruteForce in CollisionResistant/GenericAttacks.lean); \
    (2) the 2^ℓ + 1 theorems hold for every ℓ : ℕ, whereas the book illustrates small ℓ \
    (such as ℓ = 16, 2^16 + 1 = 65537). Outside check: PR #6415, review 5953780402."

register_result "birthday-collision-finder" where
  title := "The birthday collision finder finds a collision with probability at least 1/2 in \
    ⌈2√|D|⌉ + 1 hash evaluations"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Lemma 8.2", locator := "Section 8.3, p. 294" }
  ]
  theorems := [
    Cslib.Crypto.birthdayFinder_success_book,
    Cslib.Crypto.birthdayFinder_success
  ]
  scope := "For any finite nonempty message space M, oracle program digest making at most c \
    external oracle calls per message, and deterministic oracle realizing f : M → T with values \
    in a finite set D, birthdayFinder digest (ProbComp.uniform M) s samples s i.i.d. uniform \
    messages and runs bruteForceFinder digest on them, making at most s·c oracle calls on every \
    path (isQueryBounded_birthdayFinder) and never outputting a non-collision \
    (birthdayFinder_sound). In birthdayFinder_success, the probability of outputting a \
    collision in collisionOutputs f is at least 1 − exp(−s(s − 1)/(2|D|)) − C(s, 2)/|M|; \
    in birthdayFinder_success_book, when |M| ≥ 100|D| and s = ⌈2√|D|⌉ + 1, this probability is \
    at least 1/2. Deviations: (1) stated for the output of the oracle program birthdayFinder \
    rather than the sampled messages alone, with no running-time claim (sampling and the search \
    in collidingPair? are not charged); (2) |D| replaces the codomain size N = |T|, allowing any \
    finite D containing the range of f; (3) birthdayFinder_success keeps explicit error terms \
    and uses the union bound C(s, 2)/|M| in place of Theorem B.1(ii); (4) digest may be any \
    oracle program. Outside check: PR #6415, review 5953780402."

register_result "merkle-tree-position-binding" where
  title := "Merkle trees are position binding under collision resistance of the hash's domain"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 8.8",
      locator := "Version 0.6, Section 8.9.1, p. 324; the hash's domain X ∪ Y² in Section 8.9, \
        p. 320" }
  ]
  theorems := [
    Cslib.Crypto.CollisionResistantOn.merklePositionBinding
  ]
  scope := "The Merkle tree of Figure 8.12 over a polynomial-time keyed hash H with digests of \
    the key's length, so Y = {0,1}^n, and a leaf space leafSpace (the source's X, which any \
    predicate on words may be; the source's finite, efficiently recognizable and polynomially \
    bounded leaf spaces of Definition 2.9, p. 30, are instances). If H is collision resistant \
    (CollisionResistantOn, Attack Game 8.1 and Definitions 8.1–8.2, p. 290, against uniform \
    strict PPT finders) on merkleHashDomain leafSpace, the leaves and the pairs encPair (l, r) \
    of two n-bit digests, then every uniform strict PPT adversary breaks position binding \
    (MerklePositionBinding, Attack Game 8.2 and Definition 8.4) with negligible probability. \
    The verifier merkleVerify checks the path length, the position range, that every label has \
    the root's length (a Merkle proof is a list of digests, p. 321) and the recomputed root; \
    both opened leaves must lie in leafSpace. Deviations: (1) the hash takes a uniform n-bit key \
    given to the adversary, which footnote 1 on p. 290 identifies with the source's system \
    parameter; (2) digests have exactly n bits; (3) the adversary chooses the depth of the tree, \
    the length of its first path, so the game is stronger than the source's for a fixed number \
    of leaves, and MerklePositionBinding is listed as novel in the assumptions inventory for \
    that reason; (4) positions are 0 ≤ i < 2^d, padding positions included, and are written in \
    unary, which covers polynomially bounded positions but not trees indexed by \
    superpolynomially many positions. The reduction merkleCollisionFinder loses nothing \
    (succProbability_merkleBindingGame_le) and is certified strict PPT from the adversary's \
    certificate (isPPT_merkleCollisionFinder). Collision resistance on all words implies the \
    premise (merklePositionBinding_of_hashFamily, through CollisionResistantOn.mono)."

register_result "ajtai-collision-sis" where
  title := "Ajtai's hash family is collision resistant under SIS"
  topic := "cryptography"
  sources := [
    { paper := GoldreichGoldwasserHalevi1996, theorem := "Theorem 2",
      locator := "Section 3, p. 4" }
  ]
  theorems := [
    Cslib.Crypto.SIS.collisionResistantForOn_ajtaiWordHash
  ]
  scope := "Goldreich–Goldwasser–Halevi, ECCC TR96-042, Theorem 2 (Section 3, p. 4): Ajtai's \
    hash family h_A(s) = A s mod q on the words s of length m (the source's {0,1}^m), keyed by \
    a uniform A ∈ ℤ_q^{n×m}. Under SIS P (at P.β = 1, the source's Problem (A2)), every \
    uniform strict PPT finder given κ and the key ⟨κ, A⟩ finds two distinct words with equal \
    hashes only with negligible probability (CollisionResistantForOn, Boneh–Shoup \
    Definition 8.2). The reduction subtracts the two words read as 0/1 vectors and is \
    certified PPT from the finder's certificate. Deviations: (1) any SIS parameter family P \
    is allowed; the source's relations n log q < m ≤ q/(2n⁴) and q = O(n^c) are not \
    required; (2) the bound P.β must be at least 1 (hβ), since SIS P holds vacuously at \
    bound 0; (3) the column count P.m must be computable in polynomial time (hm), so that \
    the reduction can write a length-m answer for malformed words; (4) finders and solvers \
    are uniform strict PPT with negligible success, where the source's Theorem 2 is stated \
    for expected time T(n, m, q); (5) the cost of sampling the key and of evaluating the \
    hash is not certified; (6) worst-case lattice hardness (the source's Theorem 1, after \
    Ajtai) is not formalized."

register_result "nested-encryption-semantic-security" where
  title := "Nested encryption is semantically secure when all keys but one are revealed, \
    provided encryption preserves challenge admissibility (corrected Theorem 2.12)"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Theorem 2.12, corrected by the admissibility-preservation hypothesis",
      locator := "Section 2.4, p. 37" }
  ]
  theorems := [
    Cslib.Crypto.indistinguishable_nestedExperiment_of_oneTimeExperiment,
    Cslib.Crypto.advantage_nestedExperiment_eq
  ]
  scope := "A corrected form of Theorem 2.12. The book's statement omits the hypothesis \
    PreservesValid (the encryptions of an admissible pair under a supported key form an \
    admissible pair), and it fails without it: in CslibFrontierTests/Crypto/NestedEncryption.lean, \
    tagCipher_no_wrapper exhibits a one-time secure cipher (every single-key advantage is zero) \
    whose two-layer nested advantage is one. PreservesValid holds for the equal-length rule \
    whenever the length of a ciphertext is determined by the length of its message. Setting: a \
    family of ciphers E sec : Cipher K M M, whose ciphertexts lie in the message type so that \
    the n-way nested cipher E_n of p. 37 (Cipher.nested) is defined for every n. Keys are \
    indexed 0, …, n − 1 with key 0 innermost, where the book has k_1, …, k_n with k_1 innermost. \
    Keys come from a sampler sampleKey and challenge pairs are admitted by a predicate valid; \
    the hypothesis and the conclusion use the same sampleKey and valid, so the book's uniform \
    keys and equal-length rule are an instance. Hypotheses: one-time semantic security of E \
    (Attack Game 2.1 and Definition 2.2, p. 16), stated inline as Game.Indistinguishable for \
    oneTimeExperiment against uniform strict PPT two-stage adversaries with any encodable state; \
    strict PPT key sampling and encryption and polynomial-time valid; and PreservesValid. \
    Conclusion: for every constant n, the experiment of p. 37, in which the adversary chooses \
    (m₀, m₁, d) and receives the nested encryption of m_b under every key except k_d revealed, \
    is indistinguishable against uniform strict PPT two-stage adversaries; n = 0 is vacuous. The \
    keys are drawn before the adversary's choice, which gives the same law. \
    advantage_nestedExperiment_eq is NE^(n)adv[A, E] = SSadv[B, E] with \
    B = nestedToSingleAdversary, certified strict PPT (isPPT_nestedToSingleAdversary). \
    Cipher.nested_correct, in the same module, proves E_n correct when E is; it is not part of \
    Theorem 2.12 and is not listed."

register_result "cbc-mode-cpa" where
  title := "CBC mode with a random IV is CPA-secure for a block cipher"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 5.4", locator := "Section 5.4.3, p. 195" }
  ]
  theorems := [
    Cslib.Crypto.BlockCipher.PRP.indcpa_cbcEncrypt
  ]
  scope := "Cipher block chaining with a random IV (BlockCipher.cbcEncrypt: a uniform \
    E.blockLen n-bit initial value c[0], then ciphertext blocks c[j + 1] = E.encrypt n k \
    (c[j] ⊕ m[j])) for any uniform BlockCipher E with key space {0,1}^{E.keyLen n}, block \
    space X = {0,1}^{E.blockLen n}, E.PRP (Attack Game 4.1 and Definition 4.1, p. 98), and \
    super-polynomial block space Negligible (fun n => (2 ^ E.blockLen n)⁻¹). The notion is \
    many-query left-or-right CPA security (SymmetricINDCPAOn, Attack Game 5.2 and \
    Definition 5.2) against uniform strict oracle-PPT adversaries, in the standard model, on \
    equal-length pairs of whole E.blockLen n-bit blocks. The source fixes a poly-bounded cap \
    ℓ on the number of blocks; here any number is admitted, which implies the statement for \
    every ℓ. The block-cipher reductions BlockCipher.cbcToPrpDistinguisher are certified \
    oracle PPT, and BlockCipher.cbcDecrypt_cbcEncrypt proves round-trip decryption \
    correctness. Concrete bounds: BlockCipher.advantage_cbcEncrypt_le, in the same module, \
    bounds the advantage by the PRP advantages of the two fixed-bit reductions plus \
    4 * ((Q * L).choose 2 / 2 ^ E.blockLen n) for Q requests of at most L bits, a cruder \
    collision term than (5.22). advantage_cbcCpaGame_le, in CBCMode.lean, gives the typed \
    bound of two PRP advantages plus 4 * (K.choose 2 / 2 ^ n) (≤ 2 Q² ℓ² / 2 ^ n) for \
    block-mode adversaries asking at most K blocks over a finite key set; it charges no \
    running time. Outside check: PR #6325, review 5951248027."

register_result "ctr-mode-cpa" where
  title := "CTR mode is CPA-secure for a pseudorandom function"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 5.3", locator := "Section 5.4.2, p. 191" }
  ]
  theorems := [
    Cslib.Crypto.PseudorandomFunction.indcpa_ctrWordEncrypt
  ]
  scope := "Randomized counter mode (ctrWordEncrypt: a uniform n-bit initial value x, then \
    counter blocks x + j mod 2^n) from a PseudorandomFunction with n-bit keys, inputs and \
    outputs, where the security parameter n is the block length and the key is a uniform n-bit \
    word: the source's PRF over (K, X, Y) with X = {0, ..., N - 1} and Y = {0,1}^n, taken with \
    N = 2^n. The notion is many-query left-or-right CPA security (SymmetricINDCPAOn, Attack \
    Game 5.2 and Definition 5.2) against uniform strict oracle-PPT adversaries, in the standard \
    model, on equal-length pairs of whole n-bit blocks. The source caps the number of blocks at a \
    poly-bounded ℓ; here any number is admitted, which implies the capped statement. The PRF \
    reductions ctrToPrfDistinguisher are certified oracle PPT. Concrete bounds: \
    advantage_ctrWordCPAGame_le, in the same module, bounds the advantage by the PRF advantages \
    of the two fixed-bit reductions plus 2 (Q L)² / 2^n for Q requests of at most L ≤ 2^n bits, \
    a cruder collision term than the source's (5.14). advantage_ctrCpaGame_le and \
    advantage_ctrCpaGame_ctrModCounter_le, in CTRMode.lean, give the typed bound of two PRF \
    advantages plus 2 K² / 2^n for block-mode adversaries asking at most K blocks, over a finite \
    key set, for any counter schedule that is distinct within a query and injective in the IV; \
    they charge no running time."

register_result "prf-one-time-pad-cipher-cpa" where
  title := "The cipher (x, F(k, x) ⊕ m) built from a pseudorandom function F is CPA-secure"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Example 5.2, through Theorem 5.2",
      locator := "Section 5.4.1, pp. 183–184; Theorem 5.2 and its proof, pp. 184–189" }
  ]
  theorems := [
    Cslib.Crypto.PseudorandomFunction.indcpa_prfCipher
  ]
  scope := "Let F be a PseudorandomFunction: n-bit keys, inputs and outputs, deterministic \
    polynomial-time evaluation, secure against adaptive uniform oracle-PPT tests, with queries \
    of another length answered by the empty word (Attack Game 4.2 and Definition 4.2, \
    pp. 132–133). prfCipher is the cipher E₀ of Example 5.2 with K′ = X = M = {0,1}^n: a \
    uniform n-bit key k; an n-bit message m is encrypted as x ‖ (F(k, x) ⊕ m) for a fresh \
    uniform n-bit x, and decryption recomputes the pad. It is a SymmetricCipher, whose fields \
    certify strict PPT key generation and encryption, polynomial-time decryption and \
    correctness on n-bit messages. N = |X| = 2^n is super-poly. Example 5.2 obtains CPA \
    security from Theorem 5.2 with the one-time pad as the semantically secure cipher E; the \
    theorem is proved here for this cipher, and Theorem 5.2 for a general E is not formalized. \
    The notion is INDCPA (Attack Game 5.2 and Definition 5.2, pp. 181–182) against uniform \
    strict oracle-PPT adversaries in the standard model; both messages of a query have n bits, \
    and the oracle answers other queries with the empty word. The reductions \
    cpaToPrfDistinguisher are certified oracle PPT (isOraclePPT_cpaToPrfDistinguisher). \
    Asymptotic; advantage_cpaGame_prfCipher_le, in the same module, bounds the advantage of an \
    adversary making Q queries by the PRF advantages of the two fixed-bit reductions plus \
    2Q²/2^n, where (5.5) with SSadv = 0 gives 2·PRFadv + Q²/N: the collision term is twice the \
    book's because it uses a cruder union bound."

register_result "ofb-mode-cpa" where
  title := "OFB mode is CPA-secure for a pseudorandom function"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 5.15(b)", locator := "Section 5.8, p. 212" }
  ]
  theorems := [
    Cslib.Crypto.PseudorandomFunction.indcpa_ofbWordEncrypt
  ]
  scope := "OFB mode (ofbWordEncrypt: a uniform n-bit initial value x₀, chain values \
    xᵢ = F(k, xᵢ₋₁) truncated to n bits, and the ciphertext x₀ followed by the blocks mᵢ ⊕ xᵢ) \
    from a PseudorandomFunction with n-bit keys, inputs and outputs, where the security \
    parameter n is the block length and the key is a uniform n-bit word. The notion is \
    many-query left-or-right CPA security (SymmetricINDCPAOn, Attack Game 5.2 and \
    Definition 5.2) against uniform strict oracle-PPT adversaries, in the standard model, on \
    equal-length pairs of whole n-bit blocks. The exercise fixes a poly-bounded number ℓ of \
    blocks; here any number is admitted, which implies the statement for every ℓ. The PRF \
    reductions ofbToPrfDistinguisher are certified oracle PPT. Concrete bounds: \
    advantage_ofbWordCPAGame_le, in the same module, bounds the advantage by the PRF advantages \
    of the two fixed-bit reductions plus 2 (Q L) (Q L + L) / 2^n for Q requests of at most L \
    bits; the exercise states no bound. advantage_ofbCpaGame_le, in OFBMode.lean, gives the \
    typed bound of two PRF advantages plus 2 K (K + ℓ) / 2^n for block-mode adversaries asking \
    at most K blocks in total and at most ℓ per query, over a finite key set; it charges no \
    running time."

register_result "iv-stream-cipher-malleability" where
  title := "XORing a mask at least as long as the message into the body of a random-IV stream \
    ciphertext gives an encryption of the masked message"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "malleability of randomized counter mode in the chosen-ciphertext example \
        (unnumbered)",
      locator := "Section 9.2.1, pp. 360–361" }
  ]
  theorems := [
    Cslib.Crypto.ivStreamXorBody_mem_support_ivStreamEncrypt,
    Cslib.Crypto.ivStreamDecrypt_ivStreamXorBody,
    Cslib.Crypto.computableInPolyTime_ivStreamXorBody
  ]
  scope := "The book's example: from a randomized counter-mode encryption c of u ‖ m, the \
    ciphertext ĉ equal to c except that ĉ[1] := c[1] ⊕ u ⊕ v decrypts to v ‖ m (p. 361). These \
    theorems prove the property behind it for every stream cipher with a random initial value. \
    ivStreamEncrypt keystream n k msg draws a uniform n-bit IV and outputs IV followed by \
    keystream(n, k, IV, |msg|/n) ⊕ msg, for an arbitrary keystream function; randomized counter \
    mode (ctrWordEncrypt, Section 5.4.2), OFB mode and the one-block cipher prfCipher are of \
    this form. ivStreamXorBody n Δ c keeps the first n bits of c and XORs Δ into the rest; it \
    uses neither the key nor the keystream, and it is computable in polynomial time with n in \
    unary (computableInPolyTime_ivStreamXorBody). ivStreamXorBody_mem_support_ivStreamEncrypt: \
    if c is an encryption of msg and |Δ| ≥ |msg|, the result is an encryption of msg ⊕ Δ (it \
    lies in the support of that encryption). ivStreamDecrypt_ivStreamXorBody: when msg is a \
    whole number of n-bit blocks and the keystream from every n-bit IV has that many bits, it \
    decrypts to msg ⊕ Δ. The book's mask is Δ = (u ⊕ v) ‖ 0…0. Not covered: the randomized CBC \
    half of the example (ĉ[0] := c[0] ⊕ u ⊕ v) and the CRC step of the WEP malleability attack \
    (Section 9.10, Attack 3)."

register_result "prg-parallel-composition" where
  title := "The parallel composition of a secure pseudorandom generator is secure"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 3.2", locator := "Section 3.4.1, p. 55" }
  ]
  theorems := [
    Cslib.Crypto.computationallyIndistinguishable_parallelGenerator,
    Cslib.Crypto.computableInPolyTime_parallelGenerator,
    Cslib.Crypto.length_parallelGenerator
  ]
  scope := "Let G be a PseudorandomGenerator: deterministic polynomial time, n-bit seeds, \
    output length length n with strict expansion n < length n, and secure against uniform \
    strict PPT tests (Attack Game 3.1 and Definition 3.1, pp. 46–47, which require neither the \
    seed convention nor expansion). Let the repetition parameter count be computable in \
    polynomial time from 1^n, where the source asks only that it be poly-bounded. Then G applied \
    to count n independent uniform n-bit seeds, with the outputs concatenated \
    (parallelGenerator), is computationally indistinguishable from count n · length n uniform \
    bits against uniform strict PPT distinguishers that read 1^n and the word. The conclusion is \
    stated for the two ensembles indexed by n (ComputationallyIndistinguishable), not as \
    PseudorandomGenerator, which would index security by the seed length count n · n. The \
    composed generator is deterministic polynomial time (computableInPolyTime_parallelGenerator) \
    with output length count · length width (length_parallelGenerator). The hybrid reduction \
    draws its hybrid index from a padded dyadic range, so the advantage is multiplied by at most \
    2 (count n + 1), where the source's factor is count n. Asymptotic; no concrete bound is \
    stated."

register_result "prg-from-prf" where
  title := "A pseudorandom function evaluated at fixed distinct points is a pseudorandom generator"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 4.8", locator := "Section 4.4.4, p. 138" }
  ]
  theorems := [
    Cslib.Crypto.PseudorandomFunctionOver.toPRG,
    Cslib.Crypto.indistinguishable_prgFromPRF,
    Cslib.Crypto.advantage_prgFromPRF_eq
  ]
  scope := "Let F be a PseudorandomFunctionOver inLen outLen: n-bit keys, inLen n-bit inputs, \
    outLen n-bit outputs, deterministic polynomial-time evaluation, secure against adaptive \
    uniform oracle-PPT tests, with queries of another length answered by the empty word \
    (Attack Game 4.2 and Definition 4.2, pp. 132–133, allow any key space). Let x n be ℓ n \
    distinct inLen n-bit points whose list is computable in polynomial time from 1^n; the source \
    fixes ℓ ≥ 1 poly-bounded points. Then prgFromPRF, mapping an n-bit seed k to \
    F(k, x₁) ‖ … ‖ F(k, x_ℓ), is a PseudorandomGenerator of output length ℓ n · outLen n \
    (toPRG), under the extra hypothesis n < ℓ n · outLen n, because that notion includes strict \
    expansion, which Definition 3.1 does not. indistinguishable_prgFromPRF states the \
    indistinguishability without expansion, for outLen computable in polynomial time. \
    advantage_prgFromPRF_eq is the theorem's exact equality PRGadv[A, G] = PRFadv[B, F] at every \
    n and for every distinguisher A, with the explicit wrapper B = prgFromPRFReduction, which is \
    certified oracle PPT (isOraclePPT_prgFromPRFReduction)."

register_result "statistical-implies-computational-indistinguishability" where
  title := "Statistically indistinguishable distributions are computationally indistinguishable"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Corollary 3.12", locator := "Section 3.11, p. 85" }
  ]
  theorems := [
    Cslib.Crypto.StatisticallyIndistinguishable.computationallyIndistinguishable
  ]
  scope := "Ensembles X and Y : ℕ → PMF (List Bool) of words, in the asymptotic reading of \
    Section 3.11.1 (p. 87). Neither needs to be efficiently samplable, as the book allows, and \
    their supports need not be finite or of polynomially bounded length, so the book's finite \
    sets R_λ of polynomially long bit strings are a special case. Hypothesis: \
    StatisticallyIndistinguishable X Y, one negligible ε with CloseTo (X n) (Y n) (ε n) for \
    every n. CloseTo μ ν ε says that no event is more than ε likelier under μ than under ν, \
    which by Theorem 3.10 (p. 83) is the statistical distance bound Δ[μ, ν] ≤ ε of \
    Definition 3.5, so on the book's finite sets the hypothesis is Definition 3.6 (p. 85). \
    Conclusion: \
    ComputationallyIndistinguishable X Y, Attack Game 3.3 and Definition 3.4 (p. 82) against \
    uniform strict PPT distinguishers given 1^n and the sample. The proof applies \
    StatisticallyIndistinguishable.indistinguishable, which bounds every randomized test, \
    efficient or not. Theorems 3.11 and 3.13 themselves, the per-instance inequalities \
    Distadv ≤ Δ and Δ[f(X), f(Y)] ≤ Δ[X, Y], are Game.advantage_bind_le_of_closeTo and \
    CloseTo.map in other modules and are not part of this entry."

register_result "prg-output-mod-m-pseudorandom" where
  title := "A pseudorandom L-bit word reduced modulo m is a pseudorandom residue when m/2^L is \
    negligible"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Example 3.3", locator := "Section 3.11, pp. 86–87" }
  ]
  theorems := [
    Cslib.Crypto.ComputationallyIndistinguishable.map_modWord
  ]
  scope := "Hypotheses: an ensemble X of words that is computationally indistinguishable from \
    uniform words of L = length n bits (ComputationallyIndistinguishable: Attack Game 3.3 and \
    Definition 3.4, p. 82, against uniform strict PPT distinguishers). For X the output G(s) of \
    a generator on a uniform seed, this is the security of G (Attack Game 3.1 and \
    Definition 3.1, pp. 46–47), as p. 82 restates it. A modulus m n ≥ 1 computable in \
    polynomial time from unary n, and m n / 2^(length n) negligible, the book's m/N with \
    N = 2^L. Conclusion: the residue modulo m n of the word, read most significant bit first \
    and written in binary (modWord), is computationally indistinguishable from a uniform \
    residue in {0, …, m n − 1} written the same way. The book's B, which reduces its challenge \
    modulo m and runs A, is modDistinguisher, certified strict PPT (isPPT_modDistinguisher); \
    computing it is what the hypothesis on m is for. The statistical step is Example 3.2 \
    (p. 86) at N = 2^L, closeTo_uniformList_map_modWord, with the bound ≤ m/2^L in place of \
    the book's < m/N, and without the book's N ≥ m. advantage_generatorEnsemble_map_modWord_le, \
    in the same module, is the book's inequality Distadv[A, P₀, P₁] ≤ PRGadv[B, G] + m/N for \
    any generator. PseudorandomGenerator.indistinguishable_map_modWord, in the same module, is \
    the corollary for a PseudorandomGenerator, whose definition adds the strict expansion that \
    Definition 3.1 does not require; it is not listed."

register_result "lcg-one-step-distinguisher" where
  title := "Recovering the seed distinguishes the one-step linear congruential generator with \
    advantage 1 − 1/|R|"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "seed-recovery distinguisher for G_lcg (unnumbered), with a correction: \
        the book's 'clearly insecure' fails at w = q",
      locator := "Section 3.7.1, p. 70" }
  ]
  theorems := [
    Cslib.Crypto.PRG.LinearCongruential.advantage_generator_test,
    Cslib.Crypto.PRG.LinearCongruential.computableInPolyTime_test
  ]
  scope := "The generator G_lcg(s) = (⌊s/w⌋, a·s + b mod q) from S_q = {0, …, q − 1} to \
    R × S_q with R = {0, …, ⌊(q − 1)/w⌋} (generator), for parameters with q ≥ 1 and a coprime \
    to q; the book's a, b < q and 0 < w ≤ q are not assumed. The book calls G_lcg clearly \
    insecure, since s can be recovered from a·s + b mod q and ⌊s/w⌋ then distinguished from \
    random. test is that distinguisher: it computes s = a⁻¹(s′ − b) mod q and accepts when \
    ⌊s/w⌋ = r. It is deterministic and runs in time polynomial in the binary lengths of the \
    parameters and the challenge (computableInPolyTime_test). advantage_generator_test: in \
    Attack Game 3.1 (p. 46) for this finite generator, the advantage of test is exactly \
    1 − 1/|R|, at least 1/2 when 0 < w < q. At w = q, which the book allows, |R| = 1, \
    G_lcg(s) = (0, a·s + b mod q) is exactly uniform and the advantage is 0, so the book's \
    claim fails in that boundary case; the entry claims only the stated advantage. Concrete, \
    for fixed parameters, as in the book. The iterated generator G_lcg^(n) and Lemma 3.7 \
    (pp. 71–73) are not formalized."

register_result "lcg-java8-seed-recovery" where
  title := "In Boneh–Shoup's Java 8 LCG model, three integer outputs determine the seed, found \
    by a search over 2^22 candidates"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "exhaustive seed search in the book's Java 8 Math.random model (unnumbered)",
      locator := "Section 3.7.1, pp. 70–71" }
  ]
  theorems := [
    Cslib.Crypto.PRG.LinearCongruential.seedSearch_java8,
    Cslib.Crypto.PRG.LinearCongruential.computableInPolyTime_seedSearch
  ]
  scope := "java8 has the parameters that the book gives for Java 8 Math.random, q = 2^48, \
    a = 0x5DEECE66D, b = 0x0B and w = 2^22 (pp. 70–71); the entry concerns that model and its \
    integer outputs ⌊s_i/w⌋. Java's Math.random returns a double, and no correspondence with \
    that interface is formalized. seedSearch r₁ r₂ r₃ tries the w candidates r₁·w + e with \
    e < w below q and returns the greatest one whose next two outputs are r₂ and r₃, or r₁·w \
    if none is; the book tests the candidates against r₁, r₂, r₃ and states no order or fallback. \
    seedSearch_java8: for every seed s < 2^48, the search on the first three outputs \
    ⌊s_i/w⌋ of the iterated generator returns s, from which all later outputs follow. \
    computableInPolyTime_seedSearch: the search runs in time polynomial in w, given in unary, \
    and in the binary lengths of the other inputs, which is the book's 2^22 trials. \
    seedSearch_eq, in the same module, proves the search correct for any parameters under a \
    condition the book does not state (no nonzero d with |d| < w has a·d within w of a \
    multiple of q); the module documents parameters within the book's conditions \
    (q = 16, a = b = 1, w = 4) where two seeds share three outputs. The running time 'under a \
    second' and the lattice attack of Lemma 3.7 are not formalized."

register_result "perfect-security-characterizations" where
  title := "Perfect security is equivalent to equal key counts, to equal event probabilities and \
    to independence of message and ciphertext"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorems 2.1, 2.3 and 2.4",
      locator := "Section 2.1.2, pp. 8–12" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.ciphertextIndist_ofPure_uniformOfFintype_iff,
    Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.ciphertextIndist_iff_forall_toOuterMeasure,
    Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme.ciphertextIndist_iff_jointDist_eq_mul
  ]
  scope := "A Shannon cipher (E, D) over (K, M, C) with a uniform key (Section 2.1.1, p. 5) is \
    EncScheme.ofPure (uniformOfFintype K) enc dec h, where h is the correctness property \
    D(k, E(k, m)) = m. CiphertextIndist, equal ciphertext laws for any two messages, is \
    Definition 2.1 (p. 8). K is finite and nonempty; M and C are arbitrary types, where the \
    book takes them finite. Theorem 2.1 (pp. 8–9), \
    ciphertextIndist_ofPure_uniformOfFintype_iff: (i) ⇔ (ii), perfect security holds exactly \
    when for each c the number of keys with E(k, m) = c is one natural number N_c for all m; \
    (iii) is CiphertextIndist itself. Theorem 2.3 (pp. 10–11), \
    ciphertextIndist_iff_forall_toOuterMeasure: equal ciphertext laws exactly when every event \
    S ⊆ C, the book's predicate φ, has the same probability under any two messages. \
    Theorem 2.4 (pp. 11–12), ciphertextIndist_iff_jointDist_eq_mul: for a message law that \
    gives every message nonzero probability and a key drawn independently, perfect security \
    holds exactly when Pr[𝐦 = m ∧ 𝐜 = c] = Pr[𝐦 = m]·Pr[𝐜 = c] for all fixed values m and c, \
    where 𝐦 and 𝐜 are the random message and ciphertext, as in the book; this is the \
    factorization the book's proof uses. Its first half holds for every message law, as in the \
    book; that is indep_of_ciphertextIndist in the pinned cslib, another module. Theorems 2.3 \
    and 2.4 are stated for every EncScheme, randomized and with any key law, of which the \
    book's case is ofPure with a uniform key. perfectlySecret_iff_ciphertextIndist in the \
    pinned cslib converts to the posterior notion PerfectlySecret. Information-theoretic."

register_result "shannon-cipher-examples" where
  title := "The additive one-time pad is perfectly secure, the variable-length one-time pad is \
    perfectly secure only for L = 0, and the substitution cipher is not on words of length at \
    least 2 over at least two symbols"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Examples 2.5, 2.6 and 2.7",
      locator := "Section 2.1.2, pp. 9–10" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PerfectSecrecy.additiveOTP_ciphertextIndist,
    Cslib.Crypto.Protocols.PerfectSecrecy.variableLengthOTP_ciphertextIndist_iff,
    Cslib.Crypto.Protocols.PerfectSecrecy.not_ciphertextIndist_substitutionCipher
  ]
  scope := "Each cipher is EncScheme.ofPure with a uniform key, and CiphertextIndist is \
    Definition 2.1 (p. 8). additiveOTP_ciphertextIndist (Example 2.7, p. 10): the additive \
    one-time pad E(k, m) = m + k, D(k, c) = c − k is perfectly secure over every finite \
    additive group G; the book's cipher (Example 2.4, p. 7) is G = ZMod n with n positive. \
    variableLengthOTP_ciphertextIndist_iff (Example 2.5, p. 9): the variable-length one-time \
    pad of Example 2.2 (p. 6), with keys {0,1}^L and messages and ciphertexts {0,1}^{≤L}, is \
    perfectly secure exactly when L = 0. The book's counterexample uses messages of lengths 1 \
    and 2, so it assumes L ≥ 2; here every L ≥ 1 is covered. \
    not_ciphertextIndist_substitutionCipher (Example 2.6, p. 10, first paragraph): the \
    substitution cipher of Example 2.3 (p. 7) on words of L symbols of a finite alphabet is \
    not perfectly secure when L ≥ 2 and the alphabet has at least two symbols, hypotheses the \
    book leaves implicit and which cannot be dropped. additiveOTP_perfectlySecret, \
    not_perfectlySecret_variableLengthOTP and not_perfectlySecret_substitutionCipher, in the \
    same module, are the same statements for the posterior notion PerfectlySecret. \
    Information-theoretic."

register_result "luby-rackoff-prp" where
  title := "Luby–Rackoff: three Feistel rounds of a pseudorandom function give a pseudorandom \
    permutation"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 4.9",
      locator := "Section 4.5, pp. 141–143 (construction p. 141, Figure 4.14 p. 142, \
        Theorem 4.9 p. 143)" },
    { paper := LubyRackoff1988, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Crypto.PseudorandomFunction.prp_lubyRackoffCipher
  ]
  scope := "Let F be a PseudorandomFunction: n-bit keys, inputs and outputs, deterministic \
    polynomial-time evaluation, secure against adaptive uniform oracle-PPT tests. The \
    three-round Feistel cipher lubyRackoffCipher, with 3n-bit keys k₁ ‖ k₂ ‖ k₃ and 2n-bit blocks \
    u ‖ v, encrypts by w = u ⊕ F(k₁, v), x = v ⊕ F(k₂, w), y = w ⊕ F(k₃, x) and outputs \
    x ‖ y; decryption runs the rounds backwards. It is a pseudorandom permutation \
    (BlockCipher.PRP: Attack Game 4.1 and Definition 4.1, pp. 97–98, read asymptotically) \
    against uniform oracle-PPT distinguishers making adaptive forward queries. The real game \
    draws one uniform 3n-bit key, that is, three independent round keys; the ideal game draws a \
    uniform permutation of 2n-bit blocks; a query that is not 2n bits long is answered with the \
    empty word in both games. Theorem 4.9 allows any key space and half-blocks of n(λ) bits with \
    2^n(λ) super-poly; here round keys and half-blocks have exactly n bits, n being the security \
    parameter, so 2^n is super-polynomial. The cipher proved secure is the BlockCipher value \
    whose fields certify polynomial-time encryption and decryption and their mutual inversion. \
    Asymptotic; the theorem's concrete bound 3 PRFadv + Q²/N + Q²/2N² is not stated, and the \
    random-round step advantage_lubyRackoffRandomRounds_prpIdealGame_le bounds the gap to a \
    uniform permutation by 2 C(Q, 2) / 2^n + C(Q, 2) / 4^n for Q queries. The [LubyRackoff1988] \
    theorem number and locator were not checked: no copy is recorded in the manual's sources. \
    The four-round strong pseudorandom permutation in the same module is not part of this \
    entry."

register_result "linear-cryptanalysis-majority-vote" where
  title := "Linear cryptanalysis: with a linear relation of bias ε ≥ 0, a majority vote over t \
    independent uniform known plaintexts recovers a key parity bit with probability at least \
    1 − e^(−2tε²)"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Lemma 4.3, with a sharper exponent",
      locator := "Section 4.3.1, pp. 123–124 (relation (4.14), p. 123; bound (4.15), p. 124)" }
  ]
  theorems := [
    Cslib.Crypto.LinearCryptanalysis.HasLinearRelation.prob_linearKeyBitEstimate_ge
  ]
  scope := "For any keyed function E : {0,1}^h × {0,1}^n → {0,1}^n (the book: a block cipher; \
    neither invertibility nor decryption is used), masks S₀, S₁ ⊆ {0, …, n − 1} and \
    S₂ ⊆ {0, …, h − 1}, and ε ≥ 0: the book's bias is positive and non-negligible, and the \
    finite bound here also holds, trivially, at ε = 0. HasLinearRelation is (4.14): for \
    every key k, m[S₀] ⊕ E(k, m)[S₁] = k[S₂] for at least a 1/2 + ε fraction of the messages m. \
    For every key k and every t, if the known plaintexts m₁, …, m_t are independent and \
    uniform, with c_i = E(k, m_i), the majority of the \
    bits m_i[S₀] ⊕ E(k, m_i)[S₁] equals k[S₂] with probability at least 1 − exp(−2tε²), which \
    implies the printed bound 1 − exp(−tε²/2) of (4.15). The book does not say how a tied vote \
    is resolved; linearKeyBitEstimate returns the first vote on a tie and false for t = 0. \
    Only the parity bit k[S₂] is recovered, no running time or query cost is claimed, and the \
    application to DES (pp. 124–125) is not formalized."

register_result "ecb-distinct-blocks-cpa" where
  title := "ECB mode of a pseudorandom permutation is one-time semantically secure on messages of \
    distinct blocks"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 4.1",
      locator := "Section 4.1.4, pp. 102, 104–106" }
  ]
  theorems := [
    Cslib.Crypto.BlockCipher.PRP.ecb_demOneTimeKeyINDCPAOn,
    Cslib.Crypto.BlockCipher.advantage_demKeyGameOn_ecbEncrypt,
    Cslib.Crypto.BlockCipher.PRP.ecb_demOneTimeKeyINDCPAOn_one
  ]
  scope := "Over any uniform BlockCipher E (deterministic polynomial-time encryption and \
    decryption on keyLen n-bit keys and blockLen n-bit blocks, mutual inverses) that satisfies \
    E.PRP (Attack Game 4.1 and Definition 4.1, pp. 97–98, against uniform strict oracle-PPT \
    distinguishers). Word-level ECB encryption E.ecbEncrypt slices a message word into \
    blockLen n-bit blocks and concatenates their encryptions under a uniform keyLen n-bit key \
    sampled with BitString.sampleList; correctness is proved on the underlying typed cipher \
    Cipher.ecb (Cipher.ecb_correct) via flatMap_ofFn_ecbKeyPerm. For every block-count bound ℓ \
    computable in polynomial time in unary (Theorem 4.1's poly-bounded ℓ ≥ 1, made computable by \
    Definition 2.10's requirement, p. 31, that the message space X_*^{≤ℓ} be efficiently \
    recognizable; ℓ n = 0 is also covered), E.ecbEncrypt is \
    one-time semantically secure (DEMOneTimeKeyINDCPAOn, Attack Game 2.1, p. 16, against uniform \
    strict PPT two-stage adversaries, with inadmissible challenge pairs returning false in both \
    worlds) on E.ecbValid ℓ: equal-length multiples of blockLen n of at most ℓ n distinct blocks \
    each (X_*^{≤ℓ}). The certified strict oracle-PPT reduction E.ecbToPrpDistinguisher ℓ A \
    (isOraclePPT_ecbToPrpDistinguisher) satisfies the exact equation (4.3) \
    SSadv[A, E'] = 2 · BCadv[B, E] (advantage_demKeyGameOn_ecbEncrypt). At ℓ = 1, distinctness is \
    automatic (ecbValid_eq_ecbAdmissible_of_le_one), giving single-block semantic security on \
    E.ecbAdmissible (fun _ => 1) (PRP.ecb_demOneTimeKeyINDCPAOn_one, pp. 102, 104). Outside \
    check: PR #6394, review 5953812058."

register_result "ecb-two-block-not-cpa" where
  title := "ECB mode on multi-block messages is not one-time semantically secure"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Section 4.1.4 (two-block attack)",
      locator := "Section 4.1.4, pp. 103–104" }
  ]
  theorems := [
    Cslib.Crypto.BlockCipher.not_demOneTimeKeyINDCPAOn_ecbEncrypt,
    Cslib.Crypto.BlockCipher.advantage_demKeyGameOn_ecbTwoBlockAdversary
  ]
  scope := "For every uniform BlockCipher E (even a secure PRP) and block-count schedule ℓ, the \
    certified uniform strict PPT two-stage adversary E.ecbTwoBlockAdversary \
    (isPPT_ecbTwoBlockAdversary) submits m₀ = 0^(2 · blockLen n) (two equal blocks) and \
    m₁ = 0^(blockLen n) ‖ 1^(blockLen n) (two distinct blocks when 1 ≤ blockLen n) and checks \
    whether the first and second blockLen n-bit halves of the challenge ciphertext coincide. At \
    every parameter n with 2 ≤ ℓ n and 1 ≤ E.blockLen n, it achieves exact Attack Game 2.1 \
    advantage 1 against E.ecbEncrypt on E.ecbAdmissible ℓ (equal-length multiples of blockLen n of \
    at most ℓ n blocks, X^{≤ℓ}; advantage_demKeyGameOn_ecbTwoBlockAdversary), so E.ecbEncrypt \
    fails DEMOneTimeKeyINDCPAOn whenever 2 ≤ ℓ n and 1 ≤ E.blockLen n hold infinitely often \
    (not_demOneTimeKeyINDCPAOn_ecbEncrypt). Outside check: PR #6394, review 5953812058."

register_result "lagrange-interpolation-in-the-exponent" where
  title := "Lagrange interpolation, and interpolation in the exponent, in polynomial time modulo \
    the order of a prime-order group"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Lemma 22.1 and Corollary 22.2",
      locator := "Section 22.1.1, pp. 928–929" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.eval_eq_sum_lagrangeWeightNat_mul_eval,
    Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_lagrangeWeightNat,
    Cslib.Crypto.PrimeOrderGroupFamily.lagrangeCombine_eval_smul,
    Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_encode_lagrangeCombine
  ]
  scope := "The node set J ⊆ Z_q of size t is a list of natural numbers with distinct residues \
    modulo q, and the point j* is any natural number. Lemma 22.1 \
    (eval_eq_sum_lagrangeWeightNat_mul_eval): for every prime q and every polynomial ω over Z_q \
    of degree less than t, ω(j*) = Σ_{j ∈ J} λ_j ω(j), where λ_j = lagrangeWeightNat q J j j* is \
    the product of (j* − j′)/(j − j′) over the other nodes, computed on natural numbers. Its \
    efficiency clause (computableInPolyTime_lagrangeWeightNat): when q is the order of the group \
    with description d in a PrimeOrderGroupFamily, λ_j is computable in polynomial time from d, \
    J, j and j*, with no hypothesis on the nodes. The time is polynomial in the length of the \
    whole encoded input: the group description, the nodes, the index and the point. The length \
    of the encoded description bounds that of the modulus q. The clause is stated for the \
    orders of a family's groups, not for a bare prime given in binary; in Chapter 22, q is the \
    order of the group. Corollary 22.2, written \
    additively (lagrangeCombine_eval_smul): from the pairs (j, ω(j)·h) for j ∈ J, lagrangeCombine \
    returns ω(j*)·h, for every group element h and every ω of degree less than t. \
    computableInPolyTime_encode_lagrangeCombine: the encoding of that combination is computable \
    in polynomial time from d, j* and the list of nodes paired with encoded group elements. As in \
    the book, the algorithm is given neither ω nor h. Deterministic; no assumption. The \
    identities over an arbitrary field and module that Shamir sharing uses (Section 22.5.2) are \
    in another module and are not listed."

register_result "pedersen-commitment-hiding" where
  title := "Pedersen commitments are uniformly distributed at every non-identity key"
  topic := "cryptography"
  sources := [
    { paper := Pedersen1991, theorem := "Theorem 3.1 (first sentence)",
      locator := "Section 3, p. 131" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.pedersenCommitLaw_eq_uniform_of_ne_zero
  ]
  scope := "The first sentence of Theorem 3.1 says that for any s ∈ Z_q and uniform t ∈ Z_q the \
    commitment E(s, t) = g^s h^t is uniform on G_q, the order-q subgroup of Z_p^* for primes \
    q | p − 1 (Section 2, p. 130), where g and h are chosen so that nobody knows log_g h, by a \
    trusted center or a coin-flipping protocol (p. 131); that condition excludes h = 1, where \
    E(s, t) = g^s. Here the group is F.Carrier d for any prime-order group family F and \
    description d, of prime order q = F.order d, written additively with generator \
    g = F.generator d, so the commitment is m·g + r·h. For every key h ≠ 0, the source's h ≠ 1, \
    and every message m ∈ ZMod q, the law pedersenCommitLaw d h m of m·g + r·h with r exactly \
    uniform on ZMod q equals the image of a uniform exponent γ under γ ↦ γ·g, which is a \
    bijection onto the group, so the commitment is uniform on the group. The statement is at a \
    fixed group and key, with messages in ZMod q as in the source; it involves no adversary and \
    makes no efficiency claim. uniform_pedersenCommit is the same statement composed with a \
    continuation, and pedersenCommitLaw_eq_of_ne_zero and pedersen_perfectlyHidingAt derive the \
    source's reading that E(s, t) reveals no information about s: any two messages have the \
    same commitment law. The variant for generated keys and the scheme's fair-coin samplers is \
    pedersen-commitment-hiding-native."

register_result "pedersen-commitment-hiding-native" where
  title := "Pedersen commitments are statistically hiding with generated keys and fair-coin \
    sampling"
  topic := "cryptography"
  sources := [
    { paper := Pedersen1991, theorem := "Theorem 3.1 (first sentence), statistical variant",
      locator := "Section 3, p. 131" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.negligible_advantage_pedersenHidingProbGame
  ]
  scope := "A statistical variant of the first sentence of Theorem 3.1, whose exact form is \
    pedersen-commitment-hiding, for keys and commitments drawn by the scheme's own fair-coin \
    samplers. Pedersen fixes g and h, chosen so that nobody knows log_g h, by a trusted center \
    or a coin-flipping protocol (p. 131), draws t exactly uniformly and concludes that E(s, t) \
    is uniform on G_q, the order-q subgroup of Z_p^* (Section 2, p. 130). Here the group is any \
    prime-order group family, written additively, so the commitment is m·g + r·h, and the \
    conclusion is a negligible game advantage, not an equality of distributions. The game \
    pedersenHidingProbGame draws the group d from an arbitrary setup law, with no efficiency \
    condition, then the key h = α·g with α from the fair-coin program sampleExp \
    (pedersenKeyGenProb), and gives the adversary the encoded key (d, h). The adversary chooses \
    two words and receives the commitment string, without the opening, for the word selected by \
    the hidden bit, with r drawn by pedersenCommitProb, again by sampleExp; each draw is within \
    statistical distance 1/2^n of uniform on Z_q. Messages are canonical binary words of \
    naturals below q, read as elements of Z_q; if either word is not one, both worlds commit to \
    the first word. This is the hiding experiment of [BonehShoup2023], Section 8.12 (p. 344), \
    for a scheme with a public key (Section 8.12's schemes have none), played against every \
    Encryption.WordAdversary with no efficiency bound, as in unconditional hiding (p. 346). The \
    key h = 0, drawn with probability about 1/q, is the only loss besides 4/2^n of sampling \
    error: advantage_pedersenHidingProbGame_le bounds the advantage by 1/m + 4/2^n when every \
    group in the setup's support has order at least m. The theorem therefore asks that every \
    group in the support at parameter n have order at least m n > 0 with 1/m n negligible, \
    where Pedersen asks only that q be a large prime; it does not apply to groups of bounded \
    order, which the exact statement covers. At a fixed key h ≠ 0 the fair-coin bound is 2/2^n \
    (advantage_pedersenHidingProbForKey_le_of_ne_zero). The samplers in the game are the ones \
    proved correct (pedersenVerify_of_mem_support_pedersenCommitProb) and strict PPT \
    (isPPTOn_pedersenCommitProb, isPPTOn_pedersenKeyGenProb). The result is not stated as \
    CommitmentScheme.StatisticalHiding, whose commitment law takes no security parameter \
    (#6133)."

register_result "pedersen-commitment-binding" where
  title := "Pedersen commitments are computationally binding under the discrete-logarithm \
    assumption"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 10.4 and Fact 10.3",
      locator := "Section 10.6.1, pp. 414–415; binding: Section 8.12, pp. 344 and 346" },
    { paper := Pedersen1991, theorem := "Theorem 3.1 (second sentence)",
      locator := "Section 3, p. 131" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.DiscreteLog.pedersenScheme_binding_pedersenKeyDistProb
  ]
  scope := "Over any prime-order group family and setup law for the group, under the \
    discrete-logarithm assumption DiscreteLog for that setup law (Attack Game 10.4 and \
    Definition 10.6, p. 409), Pedersen's scheme pedersenScheme is binding \
    (CommitmentScheme.Binding, the binding experiment of Section 8.12, p. 344) under the key \
    law pedersenKeyDistProb: draw the group d, then h = α·g with α from the fair-coin program \
    sampleExp, within statistical distance 1/2^n of uniform on Z_q, where Theorem 10.4 draws h \
    uniformly. Adversaries are uniform strict PPT word programs reading 1^n and the encoded key \
    (d, h) and outputting (c, (m₀, o₀), (m₁, o₁)); they win when m₀ ≠ m₁ and both openings \
    verify. Messages must be canonical binary words of naturals below q, while openings may be \
    any words, read modulo q, which admits more adversaries than canonical openings would. A \
    binding break is a collision of H_dl(m, o) = g^m h^o, so the scheme is Section 8.12's \
    commitment from a collision-resistant hash (p. 346) with the hash H_dl of Section 10.6.1; \
    the explicit reduction pedersenToDLAdversary computes the logarithm as in Fact 10.3 and is \
    certified strict PPT (isPPTOn_pedersenToDLAdversary). The setup law need not be efficiently \
    samplable; the assumption is Boneh–Shoup's when it is. Asymptotic; the per-parameter bound \
    succProbability_pedersenBindingGame_pedersenKeyDistProb_le adds 1/2^n to the \
    discrete-logarithm success probability. The second sentence of [Pedersen1991], \
    Theorem 3.1, is the extraction identity: if s ≠ s' and E(s, t) = E(s', t'), then \
    t ≠ t' mod q and log_g h = (s − s')/(t' − t) mod q, which is what pedersenToDLAdversary \
    computes (extractNat_eq_of_pedersenCommit_eq). Pedersen reads it as binding unless the \
    committer can find log_g h, for g and h chosen so that nobody knows log_g h (p. 131); the \
    binding game and the discrete-logarithm assumption are Boneh–Shoup's."

register_result "dlog-from-two-representations" where
  title := "Two different representations of one group element relative to g and h give \
    log_g h = (α − α′)/(β′ − β)"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Fact 10.3", locator := "Section 10.6.1, pp. 414–415" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.extractNat_eq_of_pedersenCommit_eq,
    Cslib.Crypto.PrimeOrderGroupFamily.extractNat_eq_of_isBindingCollision_pedersenScheme
  ]
  scope := "In the group of any description d of a PrimeOrderGroupFamily, of prime order q with \
    generator g and written additively, a representation of an element relative to g and h is \
    a pair (m, r) with m·g + r·h equal to it (pedersenCommit d h m r), the book's g^α h^β. \
    extractNat_eq_of_pedersenCommit_eq: if h = α·g and two pairs (m₀, r₀) ≠ (m₁, r₁), natural \
    numbers read in Z_q, represent the same element, then extractNat q r₁ m₀ r₀ m₁, which is \
    (r₁ − r₀)⁻¹(m₀ − m₁) in Z_q, the book's (α − α′)/(β′ − β), equals α. \
    extractNat_eq_of_isBindingCollision_pedersenScheme states the same for a word-level binding \
    collision of pedersenScheme, whose two messages are distinct canonical numbers below q. \
    extractNat computes on natural numbers and inverts by Fermat's little theorem; \
    computableInPolyTime_extractNat, in DiscreteLog/Extract.lean, certifies that it is \
    polynomial time in the group description and the four binary numbers, which is the book's \
    'efficiently compute'. It is not listed because the theorems of one entry share a defining \
    module."

register_result "schnorr-sigma-protocol" where
  title := "Schnorr's Sigma protocol for discrete logarithms is complete and efficiently special \
    sound, with 2/2^n statistical closeness and computational special HVZK"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Examples 19.1–19.3",
      locator := "Section 19.4, pp. 772–774 (Definitions 19.3–19.5 and Examples 19.1–19.3); \
        Figure 19.1, Section 19.1, p. 756; Attack Game 20.4 and Definition 20.6, Section 20.4.2, \
        p. 840" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.schnorrProbFamily_complete,
    Cslib.Crypto.PrimeOrderGroupFamily.efficientSpecialSoundness_schnorrProb,
    Cslib.Crypto.PrimeOrderGroupFamily.closeTo_transcript_schnorrProbFamily_simulator,
    Cslib.Crypto.PrimeOrderGroupFamily.advantage_chvzkGame_schnorrProbFamily_le,
    Cslib.Crypto.PrimeOrderGroupFamily.computationalSpecialHVZK_schnorr
  ]
  scope := "Over any PrimeOrderGroupFamily F at index i = (n, d) with prime order q = F.order d, \
    statement u : F.Carrier d, witness α : ZMod q for the discrete-logarithm relation α • g = u \
    (Example 19.1, p. 773, written additively), and challenges in ZMod q, encoded by \
    schnorrEncoding (group elements via F.encode d and scalars in binary). In \
    F.schnorrProbFamily i (Figure 19.1, p. 756, and Example 19.1, p. 773), the honest prover \
    samples its commitment nonce with F.sampleExp n d (schnorrProbCommit, certified uniform \
    strict PPT on encodings by schnorrSigKeyGen via eval_schnorrSigKeyGen_eq_schnorrProbCommit \
    and isPPTOn_schnorrSigKeyGen) and computes r + c * α (certified deterministic polynomial \
    time on encodings by schnorrRespondBits, computableInPolyTime_schnorrRespondBits and \
    schnorrRespondBits_schnorrProbFamily), while the verifier checks z • g = t + c • u \
    (certified deterministic polynomial time by encodeSchnorrVerify and \
    efficientVerifier_schnorrProb). schnorrProbFamily_complete proves completeness \
    (Definition 19.3). efficientSpecialSoundness_schnorrProb proves efficient special soundness \
    (Example 19.2 and Definition 19.4, p. 773) via schnorrExtract and schnorrExtractWord. The \
    simulator schnorrSimulator (Example 19.3, p. 774) samples z with F.sampleExp n d and outputs \
    (z • g − c • u, z), certified uniform strict PPT by schnorrSimulateWord \
    (isPPT_schnorrSimulator) and outputting an accepting conversation with probability 1 on \
    every statement and challenge (accepts_schnorrSimulator, Definition 19.5(i)). On every valid \
    pair α • g = u and challenge c, closeTo_transcript_schnorrProbFamily_simulator bounds the \
    statistical distance between honest and simulated transcripts by 2/2^n (1/2^n from each \
    sampleExp draw); advantage_chvzkGame_schnorrProbFamily_le bounds Attack Game 20.4 advantage \
    by 2/2^n against arbitrary (even computationally unbounded) two-stage adversaries; and \
    computationalSpecialHVZK_schnorr establishes Definition 20.6 with exact zero acceptance \
    error (δ = fun _ => 0) along (setup n).map (n, ·) against all uniform strict PPT \
    CHVZKAdversary families (with no computational hardness assumption). Deviations: (1) in the \
    uniform strict-PPT fair-coin model, neither the prover nor the simulator can sample ZMod q \
    with zero error when q is not a power of two (unlike Definition 2.8, p. 30, which permits \
    negligible runtime-overflow probability and exact rejection sampling), so Definition 19.5(ii) \
    identical transcript distribution is relaxed to 2/2^n statistical closeness and Definition \
    20.6 ComputationalSpecialHVZK with exact Definition 19.5(i) acceptance; (2) the challenge \
    space is C = ZMod q (the 2/2^n transcript bound holds pointwise at every c : ZMod q and thus \
    for any subset C ⊆ ZMod q, while Attack Game 20.4 draws c uniformly from ZMod q); (3) groups \
    are written additively and setup : ℕ → PMF F.Desc is arbitrary."

register_result "schnorr-identification-direct-dl" where
  title := "Schnorr identification is secure against direct attacks under the discrete-logarithm \
    assumption"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 19.1",
      locator := "Section 19.1, p. 757 (Theorem 19.1 with (19.1) and (19.2)); protocol: \
        Figure 19.1, p. 756; attack: Attack Game 18.1 and Definition 18.2, p. 720" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.negligible_schnorrDirectProbGame
  ]
  scope := "Over any prime-order group family F and setup law setup : ℕ → PMF F.Desc, under the \
    discrete-logarithm assumption F.DiscreteLog setup (Attack Game 10.4 and Definition 10.6, \
    p. 409). Schnorr's protocol (Figure 19.1) is written additively, u = α·g, and group \
    elements, commitments and responses are binary words: the verifier accepts when the \
    commitment word encodes z·g − c·u, with the challenge and response words read as numbers \
    modulo q. The challenge set is the k n-bit words read modulo q, a power-of-two subset of Z_q \
    that embeds injectively when 2^(k n) ≤ q, in place of an arbitrary C ⊆ Z_q. Premises: k is \
    computable in polynomial time, 2^(k n) ≤ q for every group in the support of setup n, and \
    2^(−k n) is negligible (the source's super-poly N = |C|). The game is schnorrDirectProbGame \
    (Attack Game 18.1): the key comes from the scheme's fair-coin key generator \
    schnorrSigKeyGen, whose exponent sampleExp is within statistical distance 2^(−n) of uniform \
    on Z_q, and the challenge is an exactly uniform k n-bit word. Adversaries are uniform strict \
    PPT two-stage word programs reading 1^n, the group description and the encoded public key \
    (SchnorrImpersonator.IsPPT); the conclusion is that each succeeds with negligible \
    probability (Definition 18.2). The proof applies DiscreteLog to the rewinding adversary \
    A.rewind k through its certificate isPPTOn_rewind. The per-parameter bound \
    succProbability_schnorrDirectProbGame_le is ε ≤ 2^(−n) + 2^(−k n) + √ε′, the source's \
    (19.2) plus the sampler's error; no concrete running-time statement, such as the source's \
    factor two, is made. The setup law is arbitrary: the assumption is Boneh–Shoup's when setup \
    is sampled efficiently with descriptions of polynomial length, as for the system \
    parameterization of Section 10.5.2 (Definition 10.9, p. 413). Asymptotic."

open Cslib.Crypto.PrimeOrderGroupFamily in
register_result "schnorr-leaked-nonce-key-recovery" where
  title := "Leaked Schnorr signing randomness reveals the signing key: for an m-bit random-oracle \
    challenge with 2^m ≤ q, the attack fails with probability at most 2^(−m), and only on the \
    zero challenge"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "leaked Schnorr signing randomness reveals the signing key (unnumbered remark)",
      locator := "Section 21.2, p. 861 (paragraph 'Erasing ephemeral data'); Schnorr \
        signatures: Section 19.2, pp. 762–763" }
  ]
  theorems := [
    schnorrRelatedNonceExtractWord_schnorrSignCoins,
    isOraclePPTOn_schnorrLeakedNonceWordAdversary,
    one_sub_inv_two_pow_le_succProbability_schnorrLeakedNonceWordGame
  ]
  scope := "For any prime-order group family F, security parameter n, group description d of \
    order q, challenge length m with 2^m ≤ q, and message msg. schnorrLeakedNonceWordGame draws \
    the key pair with the scheme's fair-coin key generator schnorrSigKeyGen and the nonce r with \
    sampleExp, and signs msg by the steps of the native signer schnorrROMSign against an m-bit \
    stateful random oracle: commitment r·g, challenge c the oracle's m-bit answer on the message \
    and commitment, read modulo q, and response r + c·α. The adversary receives d, m, msg, the \
    signature and the leaked nonce, as the word of r mod q, which the raw sampleExp bits \
    determine; it does not receive the public key. It wins if it outputs the word of the secret \
    key α. schnorrLeakedNonceWordAdversary makes one oracle query, to recompute c, and outputs \
    (z − r)/c; it is uniform strict oracle PPT, with m in unary \
    (isOraclePPTOn_schnorrLeakedNonceWordAdversary). \
    one_sub_inv_two_pow_le_succProbability_schnorrLeakedNonceWordGame: it wins with probability \
    at least 1 − 2^(−m), that is, it fails with probability at most 2^(−m); no equality is \
    claimed. schnorrRelatedNonceExtractWord_schnorrSignCoins: from an honest signature whose \
    challenge is nonzero modulo q, the recovery always returns the key. Since 2^m ≤ q, only the \
    all-zero challenge word is zero modulo q, so failure can occur only on that challenge, where \
    z = r carries no information about α; the book's 'trivially compute' holds except on that \
    event. The game signs one fixed message. The remark appears in the book's discussion of key \
    exchange; only its claim about Schnorr signatures is formalized."

register_result "schnorr-identification-eavesdropping-dl" where
  title := "Schnorr identification is secure against eavesdropping attacks under the \
    discrete-logarithm assumption"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorems 19.1 and 19.5 combined",
      locator := "Section 19.1: Theorem 19.1, p. 757; Theorems 19.3–19.5, pp. 761–762; \
        attack: Attack Game 18.2 and Definition 18.6, pp. 733–734" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.negligible_schnorrEavesdropProbGame,
    Cslib.Crypto.PrimeOrderGroupFamily.schnorr_isProbEavesdropSecure_of_discreteLogHard
  ]
  scope := "Theorems 19.1 and 19.5 combined: under the discrete-logarithm assumption, Schnorr \
    identification is secure against eavesdropping attacks. Theorem 19.5 on its own (security \
    against direct attacks implies security against eavesdropping) is not stated. The group \
    family, setup law and assumption, the additive notation and binary word encodings, the \
    power-of-two k n-bit challenge set, the adversary class and the premises (k computable in \
    polynomial time, 2^(k n) ≤ q on the support of setup n, 2^(−k n) negligible) are as in \
    schnorr-identification-direct-dl; in addition the conversation count Q is computable in \
    polynomial time. The game schnorrEavesdropProbGame (Attack Game 18.2) draws the key with \
    schnorrSigKeyGen and gives the adversary Q n independent honest conversations for that key \
    from the scheme's strict-PPT prover schnorrRealTranscript, whose commitment exponent comes \
    from sampleExp and whose challenge is an exactly uniform k n-bit word. \
    IsProbEavesdropSecure (Definition 18.6) quantifies over every polynomial-time Q and every \
    uniform strict PPT eavesdropper; the source's adversary chooses how many conversations to \
    request, and a bounded one is covered by a Q that it may partly ignore. The proof turns the \
    eavesdropper into the direct impersonator A.toDirect k Q, which simulates the conversations \
    with the strict-PPT simulator (certified by isPPT_toDirect), and applies DiscreteLog to its \
    rewinding adversary through isPPTOn_rewind. Where Theorem 19.5 has the exact equality \
    ID2adv[A, I] = ID1adv[B, I] (from Theorems 19.3 and 19.4, p. 761), the fair-coin key \
    generator and simulator add the statistical term (2 Q n + 1)·2^(−n) \
    (succProbability_schnorrEavesdropProbGame_le), so the combined asymptotic endpoint is \
    stated, not the source's exact finite equality. No concrete running-time statement is made. \
    The setup law is arbitrary, as in schnorr-identification-direct-dl. Asymptotic."

register_result "schnorr-identification-guessing-attack" where
  title := "Schnorr identification with k n-bit challenges: an efficient guessing impersonator \
    succeeds with probability at least 2^(−k n), so security requires 2^(−k n) negligible"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "guessing attack showing that the challenge space must be super-poly \
        (unnumbered)",
      locator := "Section 19.1.1, p. 762; protocol and key generation: Figure 19.1, p. 756" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.inv_two_pow_le_succProbability_schnorrDirectGame,
    Cslib.Crypto.PrimeOrderGroupFamily.isPPT_schnorrGuessingImpersonator,
    Cslib.Crypto.PrimeOrderGroupFamily.negligible_inv_two_pow_of_negligible_schnorrDirectGame
  ]
  scope := "Schnorr's protocol over a PrimeOrderGroupFamily with group parameters from any setup \
    law, written additively, with the word encodings, verifier and challenges of \
    schnorr-identification-direct-dl: a challenge is a uniform k n-bit word read modulo q. The \
    game is schnorrDirectGame, Attack Game 18.1 (p. 720) with the secret key α drawn exactly \
    uniformly on Z_q, as the book's key generator draws it (p. 756), and not with the library's \
    fair-coin key generator of schnorrDirectProbGame, the game of the registered security \
    theorems; the two games differ by at most 1/2^n \
    (advantage_schnorrDirectProbGame_schnorrDirectGame_le). The impersonator \
    schnorrGuessingImpersonator m runs the word-level simulator schnorrSimulatedTranscript on a \
    uniform m n-bit challenge, sends the simulated commitment and answers every challenge with \
    the simulated response, as the book's adversary does. \
    inv_two_pow_le_succProbability_schnorrDirectGame: whenever m n ≤ k n it wins with \
    probability at least 1/2^(k n), which is the book's 1/|C| when 2^(k n) ≤ q. \
    isPPT_schnorrGuessingImpersonator: it is uniform strict PPT when m is computable in \
    polynomial time in unary. negligible_inv_two_pow_of_negligible_schnorrDirectGame: if every \
    uniform strict PPT impersonator wins schnorrDirectGame with negligible probability, then \
    2^(−k n) is negligible, the book's conclusion that |C| must be super-poly; it uses the \
    impersonator with m = 0, so no condition on k is needed. The generic Sigma-protocol bound \
    SpecialHVZK.inv_card_le_succProbability_directAttack (Exercise 19.7) has no cost model and \
    is not part of this entry."

register_result "elgamal-ddh-ind-cpa" where
  title := "Multiplicative ElGamal is semantically secure under DDH"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 11.5(a)", locator := "Section 11.8, p. 459" }
  ]
  theorems := [
    Cslib.Crypto.DecodablePrimeOrderGroupFamily.DDH.indcpaOn_elGamalGroupEncryptProb
  ]
  scope := "The scheme E_MEG of the exercise, encrypting a group element m as \
    (β·g, β·u + m) in additive notation, over a decodable prime-order group family, whose \
    membership test is polynomial time (the efficiently recognizable groups of \
    Definition 10.9(1), p. 413). The group is a deterministic polynomial-time schedule d, the \
    group at parameter n being d n, in place of a randomized system parameterization; DDH \
    (Attack Game 10.6 and Definition 10.8, pp. 410–411) is assumed for the point-mass setup at d, \
    which is efficiently samplable, and the public key word carries d n alongside u. Key \
    generation and encryption are the scheme's own fair-coin strict PPT programs \
    (elGamalKeyGenProb, elGamalEncryptProb), which draw each exponent with sampleExp, within \
    statistical distance 1/2^n of uniform on Z_q. The notion is single-challenge IND-CPA \
    (INDCPAOn: Attack Game 11.1 and Definition 11.2, pp. 436–437) against uniform strict PPT \
    two-stage adversaries reading 1^n. Equipping each public group F.Carrier (d n) with a \
    constant effective-length function (Section 2.3.2, Definition 2.9 and Example 2.13(4), \
    pp. 30–31; Definition 11.3(2), pp. 437–438), a challenge pair is admissible under Attack \
    Game 11.1's equal-effective-length condition whenever both words encode elements of d n \
    (elGamalGroupValid), as distinguished from equality of serialized bit lengths; an \
    inadmissible pair makes both experiments output false. Decryption correctness on the same \
    programs is elGamalDecryptDet_elGamalEncryptProb. Asymptotic; the exercise's exact concrete \
    forward bound 2ε remains open."

register_result "dh-anonymous-key-exchange-iff-cdh" where
  title := "Diffie–Hellman anonymous key exchange is key-guessing secure if and only if CDH holds"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "security of Diffie–Hellman key exchange (unnumbered)",
      locator := "Section 10.4.2, p. 408; Attack Game 10.1 and Definition 10.1, Section 10.1, \
        p. 400" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.dhKeyExchangeProb_anonKESecure_iff_cdh,
    Cslib.Crypto.PrimeOrderGroupFamily.advantage_anonKEGame_dhKeyExchangeProb_cdhGame_le
  ]
  scope := "Over any PrimeOrderGroupFamily F and setup law setup : ℕ → PMF F.Desc, \
    F.dhKeyExchangeProb setup draws group parameters d from setup n and runs dhExecutionProb n d \
    (Figure 10.2, pp. 407–408), written additively: Alice and Bob sample exponents x, y with \
    F.sampleExp n d (within statistical distance 1/2^n of uniform on ZMod q), exchange \
    hA = x·g and hB = y·g, and output x·hB and y·hA. Correctness and honest-party efficiency \
    are proved on the same protocol in KeyExchange.lean (dhKeyExchangeProb_correct and \
    isPPTOn_dhExecutionProb). AnonKESecure (Attack Game 10.1 and Definition 10.1, p. 400, \
    called 'secure against an eavesdropper' in the book) requires every uniform strict PPT \
    KeyGuesser reading (1^n, transcript) to guess Alice's key with negligible probability; \
    F.CDH setup is Attack Game 10.5 and Definition 10.7 (pp. 409–410, asymptotic form with \
    Section 10.5.2, pp. 413–414). advantage_anonKEGame_dhKeyExchangeProb_cdhGame_le bounds \
    |AnonKEadv[A, dhKeyExchangeProb] − CDHadv[dhToCDHAdversary A, F]| ≤ 2/2^n (and conversely \
    via cdhToDHKeyGuesser, since dhToCDHAdversary (cdhToDHKeyGuesser B) = B is definitional; \
    both conversions preserve strict PPT via isPPT_dhToCDHAdversary and \
    isPPT_cdhToDHKeyGuesser). Deviations: (1) Correct and honest-party efficiency are unbundled \
    from KeyExchange rather than built into protocol syntax (Correct.anonKEGame_eq_bobKey \
    identifies guessing Alice's key with guessing Bob's key); (2) honest parties sample \
    exponents from fair coins with sampleExp rather than exact uniform ZMod q draws, incurring \
    at most 2/2^n statistical loss against cdhGame; (3) DHTranscript carries \
    groupParameters : F.Desc and setup need not be efficiently samplable, matching F.CDH setup \
    (agrees with Definition 10.9, p. 413, when setup is efficiently samplable). Asymptotic."

register_result "elgamal-ind-cpa-iff-ddh" where
  title := "Multiplicative ElGamal is semantically secure if and only if DDH holds"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 11.5(a)–(b)",
      locator := "Section 11.8, p. 459" }
  ]
  theorems := [
    Cslib.Crypto.DecodablePrimeOrderGroupFamily.indcpaOn_elGamalGroupEncryptProb_iff_ddh,
    Cslib.Crypto.PrimeOrderGroupFamily.ddh_of_indcpaOn_elGamalGroupEncryptProb
  ]
  scope := "The scheme E_MEG of Exercise 11.5 in additive group notation ((β·g, β·u + m) under \
    public key u = α·g) at a deterministic polynomial-time group schedule d : ℕ → F.Desc, with \
    fair-coin strict PPT key generation and encryption (elGamalKeyGenProb, elGamalEncryptProb, \
    drawing exponents with sampleExp) and deterministic decryption correctness \
    elGamalDecryptDet_elGamalEncryptProb. Equipping each public group F.Carrier (d n) with a \
    constant effective-length function (Section 2.3.2, Definition 2.9 and Example 2.13(4), \
    pp. 30–31; Definition 11.3(2), pp. 437–438), Attack Game 11.1's equal-effective-length \
    condition (pp. 436–437) admits every pair of encoded group elements at d n—distinguishing \
    constant effective length on the group from equality of serialized wire lengths, so the \
    reverse reduction's pair (encode 0, encode (c·g)) is admissible even when serialized wire \
    lengths differ. In ddh_of_indcpaOn_elGamalGroupEncryptProb (part (b), whose contrapositive mt \
    gives ¬ DDH → ¬ INDCPAOn), single-challenge IND-CPA (INDCPAOn) against uniform strict PPT \
    two-stage adversaries for any admissibility predicate admitting all encoded group-element \
    pairs at d n implies DDH (Attack Game 10.6 and Definition 10.8, pp. 410–411) on the \
    point-mass setup PMF.pure (d n), via the certified strict-PPT reduction \
    ddhWordToElGamalAdversary (isPPT_ddhWordToElGamalAdversary) and quantitative bound \
    advantage_ddhGame_le_gameOn (+ 5/2^n from fair-coin sampleExp). Combining with \
    DDH.indcpaOn_elGamalGroupEncryptProb (part (a)) yields \
    indcpaOn_elGamalGroupEncryptProb_iff_ddh over any DecodablePrimeOrderGroupFamily with \
    admissibility elGamalGroupValid. Asymptotic; the exact concrete forward bound 2ε of \
    Exercise 11.5(a) remains open."

register_result "elgamal-multiplicative-homomorphism" where
  title := "Multiplicative ElGamal ciphertexts combine homomorphically"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 11.5(c)", locator := "Section 11.8, p. 459" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.elGamalAddCiphertext_mem_support_elGamalEncryptProb,
    Cslib.Crypto.PrimeOrderGroupFamily.elGamalDecryptDet_elGamalAddCiphertext,
    Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_elGamalAddCiphertext,
    Cslib.Crypto.PrimeOrderGroupFamily.elGamalEncrypt_add,
    Cslib.Crypto.PrimeOrderGroupFamily.elGamalDecrypt_add
  ]
  scope := "The scheme E_MEG of Exercise 11.5 in additive group notation over a \
    PrimeOrderGroupFamily F. Algebraically, componentwise addition on F.Carrier d × F.Carrier d \
    sends encryptions under u with plaintexts m₁, m₂ and exponents β₁, β₂ to the encryption of \
    m₁ + m₂ with exponent β₁ + β₂ (elGamalEncrypt_add) and commutes with decryption \
    (elGamalDecrypt_add). On framed bit-word ciphertexts encPair encBits encBits (encode v, \
    encode e), elGamalAddCiphertext applies F.add to both components in deterministic polynomial \
    time (computableInPolyTime_elGamalAddCiphertext). For any honest key pair in the support of \
    elGamalKeyGenProb d n and any ciphertexts ct₁, ct₂ in the supports of elGamalEncryptProb for \
    encode m₁ and encode m₂, elGamalAddCiphertext (d n) ct₁ ct₂ lies in the support of \
    elGamalEncryptProb for encode (m₁ + m₂) (elGamalAddCiphertext_mem_support_elGamalEncryptProb) \
    and decrypts via elGamalDecryptDet to encode (m₁ + m₂) \
    (elGamalDecryptDet_elGamalAddCiphertext)."

register_result "projective-hash-universal" where
  title := "The Cramer–Shoup projective hash is universal and its tagged form universal₂: exact \
    joint laws off the Diffie–Hellman pairs"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Lemmas 12.5 and 12.7",
      locator := "Section 12.5.1, p. 485; Section 12.5.2, pp. 487–488" }
  ]
  theorems := [
    Cslib.Crypto.ProjectiveHash.uniform_projHash_apply_of_ne,
    Cslib.Crypto.ProjectiveHash.uniform_projHash2_apply_of_ne
  ]
  scope := "A group of a PrimeOrderGroupFamily, of prime order q with generator g, written \
    additively, so the book's v^σ w^τ is σ·v + τ·w. Elements are written u = α·g, v = β·g and \
    w = γ·g, which covers every element, and (u, v, w) is a Diffie–Hellman triple exactly when \
    γ = αβ (isDHTriple_generator_smul_iff). Lemma 12.5 (uniform_projHash_apply_of_ne): for \
    uniform independent σ, τ ∈ Z_q and γ ≠ αβ, the pair (σ·g + τ·u, σ·v + τ·w) of (12.14) and \
    (12.13) equals each (h, z) ∈ G² with probability exactly 1/q². Lemma 12.7 \
    (uniform_projHash2_apply_of_ne): for uniform independent σ₁, τ₁, σ₂, τ₂ ∈ Z_q, two pairs \
    (v, w) and (v̂, ŵ) off the Diffie–Hellman triples and tags ρ ≠ ρ̂, the tuple of (h₁, h₂) \
    from (12.17) and the values f′(v, w, ρ) and f′(v̂, ŵ, ρ̂) of (12.16) equals each value in \
    G⁴ with probability exactly 1/q⁴; the printed statement writes ρ₁ and ρ₂ in the exponents \
    for ρ and ρ̂. The projective evaluation on L_u (projHash_smul_generator, \
    projHash2_smul_generator) is in the same module. Information-theoretic: no assumption and \
    no adversary."

register_result "projective-hash-games" where
  title := "Universal projective hashing hides the challenge value, and universal₂ guesses win \
    with probability at most Q/q, against unbounded adaptive adversaries"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Lemmas 12.6 and 12.8, in the adaptive games of Exercise 12.26(a)–(b)",
      locator := "Section 12.5.1, p. 486; Section 12.5.2, p. 488; Section 12.11, p. 521" }
  ]
  theorems := [
    Cslib.Crypto.ProjectiveHash.universalDistExperiment_false_eq_true,
    Cslib.Crypto.ProjectiveHash.succProbability_universal2GuessGame_le
  ]
  scope := "Attack Games 12.4 and 12.5 in the adaptive form of Exercise 12.26, over a group of a \
    PrimeOrderGroupFamily of prime order q: the adversary chooses u, receives h (or (h₁, h₂)), \
    makes evaluation queries, chooses (v, w) (and ρ), receives z, and makes more evaluation \
    queries. The book's non-adaptive games are the case in which the second stage makes no \
    query, chooses (v, w) (and ρ) independently of h (or (h₁, h₂)), and keeps h in its state \
    for the last stage. Adversaries are randomized oracle programs with no bound on their \
    computation, and the keys σ, τ (or σ₁, τ₁, σ₂, τ₂) are uniform on Z_q. \
    universalDistExperiment_false_eq_true (Lemma 12.6 and Exercise 12.26(a)): for every \
    admissible adversary, the experiment with z = f(v, w) and the one with z uniform on G have \
    the same output law. Admissibility for this game: for every u and state the first stage can \
    output, the second stage's evaluation queries lie in L_u for every h, and after every \
    second-stage output (v, w, st) reachable with honest keys, (v, w) ∉ L_u and the last \
    stage's queries lie in L_u for every z. succProbability_universal2GuessGame_le (Lemma 12.8 \
    and Exercise 12.26(b)): an admissible adversary wins with probability at most Q/q, where it \
    wins if some output tuple (ẑ, v̂, ŵ, ρ̂) has (v̂, ŵ) ∉ L_u, ρ̂ ≠ ρ and \
    ẑ = f′(v̂, ŵ, ρ̂), as in Attack Game 12.5. Admissibility for this game: the second stage's \
    queries lie in L_u for \
    every (h₁, h₂); after every second-stage state reachable with honest keys, for every z, the \
    last stage's queries lie in L_u, and its output list has at most Q tuples when it runs \
    against any keys σ₁′, τ₁′, σ₂′, τ₂′, chosen independently of those of the run. Deviations: \
    (1) evaluation queries must lie in L_u on every execution path, whatever the oracle replies, \
    where the book (p. 486) assumes this of the queries made in the game; (2) the list bound is \
    required for every z and every final-stage keys, where the book counts the tuples output in \
    the game; truncating the list to its first Q tuples leaves every play of the game unchanged, \
    so a book adversary that outputs at most Q tuples meets the bound after truncation; (3) the \
    second game does not require (v, w) ∉ L_u, so it admits more adversaries than the book's. \
    Information-theoretic: no assumption."

register_result "hashed-elgamal-ddh-kdf-cpa" where
  title := "Hashed ElGamal (the variant E′_EG) is semantically secure under DDH and a secure KDF"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 11.5 (for the variant E′_EG of Remark 11.1)",
      locator := "Section 11.5.2, Theorem 11.5, pp. 449–451; Section 11.5, Remark 11.1, p. 446" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.DDH.wordINDCPA_hybrid_hashedElGamal,
    Cslib.Crypto.PrimeOrderGroupFamily.DDH.indcpaOn_hybrid_hashedElGamal,
    Cslib.Crypto.PrimeOrderGroupFamily.DDH.indcpaOf_hybrid_hashedElGamal
  ]
  scope := "Asymptotic, standard model. The scheme is the variant E′_EG of Remark 11.1: \
    encapsulation (hashedElGamalEncapsProb) sends v = b • g and derives the key H(d, w) from \
    w = b • u alone, where Theorem 11.5's E_EG hashes (v, w). Remark 11.1 states that the \
    security results of Chapter 11 hold for E′_EG as well as for E_EG. The group comes from a \
    PrimeOrderGroupFamily through a deterministic group schedule d : ℕ → F.Desc computable in \
    polynomial time from unary n: the system parameterization P(λ) of Section 10.5.2 (p. 413) \
    taken deterministic, so randomized parameter generation is not covered. Key generation and \
    encapsulation draw exponents with the fair-coin sampler sampleExp, within statistical \
    distance 1/2^n of uniform, and are uniform strict PPT; H is polynomial-time and the \
    symmetric cipher is uniform strict PPT with uniform keyLen n-bit keys. Hypotheses: DDH for \
    the setup PMF.pure (d n) (Attack Game 10.6); SecureKDF for H, which is Attack Game 11.3 for \
    the hash of one group element, with two independent uniform group elements public and keys \
    uniform keyLen n-bit words; and one-time semantic security of the cipher (Attack Game 2.1). \
    Conclusion: single-challenge IND-CPA (Attack Game 11.1, two-experiment advantage) of the \
    KEM–DEM hybrid against uniform strict PPT two-stage adversaries. \
    wordINDCPA_hybrid_hashedElGamal holds the cipher and the scheme to the source's equal-length \
    rule on bit-word messages; indcpaOn_hybrid_hashedElGamal takes for both any polynomial-time \
    admissibility predicate that ignores the public key; indcpaOf_hybrid_hashedElGamal admits \
    every pair for both, the source's notion when all messages have one length. The proof \
    applies DDH and SecureKDF to certified uniform strict PPT reductions to obtain KEM security \
    of E′_EG (DDH.kemINDCPA_hashedElGamalEncapsProb, Games 0–2 of the proof of Theorem 11.5), \
    then the KEM–DEM composition of Exercise 11.9(b) (p. 461). No concrete bound in the form \
    of (11.14) is stated for the encryption scheme."

register_result "leftover-hash-secure-kdf" where
  title := "Binary matrix hashing with a public random seed is an unconditionally secure KDF for \
    hashed ElGamal when 2^ℓ/q is negligible"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "unconditionally secure KDF from a universal hash and the leftover hash lemma \
        (unnumbered), with Theorem 8.11 at m = 1 and α = 0",
      locator := "Section 11.5.2, p. 449; Theorem 8.11: Section 8.10.4, p. 334; Attack \
        Game 11.3 and Definition 11.5, pp. 448–449" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.secureKDF_linearHashKDF,
    Cslib.Crypto.PrimeOrderGroupFamily.advantage_kdfGame_linearHashKDF_le,
    Cslib.Crypto.PrimeOrderGroupFamily.secureKDF_linearHashKDF_const,
    Cslib.Crypto.PrimeOrderGroupFamily.exists_secureKDF_withSeed
  ]
  scope := "Over any PrimeOrderGroupFamily F and setup law. The hash key is a public system \
    parameter, as p. 334 allows: F.withSeed adds a seed word s to the group description, and \
    seededSetup draws d from the setup law, then s uniform of length ℓ·(2b + 1), independently \
    of the group exponents, where ℓ = msgLen n is the key length and b = bound d bounds the \
    length of encoded group elements. linearHashKDF pads the encoding of a group element \
    injectively to 2b + 1 bits and multiplies it by s read as an ℓ × (2b + 1) binary matrix, a \
    (1/2^ℓ)-universal hash, so α = 0 in Theorem 8.11. The notion is SecureKDF: Attack Game 11.3 \
    for the hash of one group element, the key derivation of the variant E′_EG of Remark 11.1, \
    as its assumptions-inventory row records. The distinguisher sees (d, s), two independent \
    uniform group elements, and either the hash of a third or a uniform ℓ-bit key. \
    advantage_kdfGame_linearHashKDF_le: if every group in the support of setup n has order at \
    least qMin > 0, encodings of at most b bits and key length ℓ, then every distinguisher, \
    with no efficiency bound, has advantage at most √(2^ℓ/qMin)/2, Theorem 8.11's bound \
    (1/2)√(Nγ) with N = 2^ℓ and guessing probability γ = 1/q ≤ 1/qMin. \
    secureKDF_linearHashKDF: under LinearHashKDFConditions, which add that 2^ℓ/qMin n is \
    negligible, linearHashKDF is a SecureKDF against uniform strict PPT distinguishers, with no \
    computational assumption. secureKDF_linearHashKDF_const fixes a constant key length k and \
    asks that 1/qMin n be negligible. exists_secureKDF_withSeed adds a polynomial-time seed \
    length and a polynomial-time hash with k-bit outputs, so every family whose orders have a \
    lower bound qMin with 1/qMin negligible has such a KDF. linearHashKDF is polynomial time \
    whenever ℓ and b are (computableInPolyTime_linearHashKDF). DDH.withSeed, in the same \
    module, transfers DDH to the seeded family when the seed length is polynomial time; it has \
    no counterpart in the book and is not listed. The hashed ElGamal corollary \
    DDH.negligible_hashedElGamalCPAGame_ideal_linearHashKDF draws its exponents exactly and is \
    a step, not part of this entry."

register_result "cramer-shoup-ddh-cca" where
  title := "Multiplicative Cramer–Shoup is CCA secure under DDH and a collision-resistant hash"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 12.27",
      locator := "Section 12.11, pp. 521–522; proof method of Theorem 12.9, Section 12.5.3, \
        p. 489; Theorem 12.1, p. 468, and its extension to associated data, p. 502" }
  ]
  theorems := [
    Cslib.Crypto.DecodablePrimeOrderGroupFamily.DDH.indcca2ADOn_cramerShoup_bitStringAD,
    Cslib.Crypto.DecodablePrimeOrderGroupFamily.DDH.indcca2On_cramerShoup,
    Cslib.Crypto.DecodablePrimeOrderGroupFamily.DDH.indcca2InterleavedOn_cramerShoup,
    Cslib.Crypto.DecodablePrimeOrderGroupFamily.DDH.indcca2MultiOn_cramerShoup
  ]
  scope := "The scheme E_MCS of the exercise (v = β·g, w = β·u, e = β·h + m, \
    ρ = H'(v, w, e, ad), z' = β·(h₁ + ρ·h₂), in additive notation) over a decodable prime-order \
    group family (efficiently recognizable groups, Definition 10.9(1), p. 413), at a \
    deterministic polynomial-time group schedule d in place of a sampled system parameter. \
    Assumptions: DDH (Definition 10.8, p. 411) for the point-mass setup at d, and collision \
    resistance (Attack Game 8.1 and Definition 8.1, p. 290) of the hash H' = H mod q, keyed by \
    d n and a uniform keyLen n-bit hash key, with H, d and keyLen polynomial time, on the \
    exercise's domain G³ × D only: the canonically framed tuples (v, w, e, ad) of group-element \
    words and an associated-data word (isCramerShoupHashInput, characterized by \
    isCramerShoupHashInput_iff). With associated data, D = {0,1}* (encAD = encBits), because \
    decryption hashes whatever associated-data word a query carries; without it, D = {[]}. A \
    general encoded associated-data space, with collision resistance only on G³ × D, needs \
    decryption to reject associated data outside D and is open (#5293). One deviation concerns \
    the hash: key generation draws the hash key and publishes it in the public key, where the \
    exercise's H' is fixed with the group. The premises 0 < m n ≤ q(d n) with 1/m n negligible \
    add no assumption: DDH implies that 1/q(d n) is negligible (DDH.cdh and \
    CDH.negligible_inv_order), so m n = q(d n) meets them. The scheme's own fair-coin programs \
    (cramerShoupKeyGenProb and the encryption programs) draw the seven key exponents and the \
    encryption exponent with sampleExp, each within statistical distance 1/2^n of uniform on \
    Z_q; decryption is deterministic polynomial time and checks the framing and the group \
    membership of v, w and e. A challenge pair is admissible when both words encode group \
    elements (cramerShoupValid); an inadmissible pair makes both experiments output false. \
    Notions, all against uniform strict oracle-PPT adversaries reading 1^n: \
    indcca2ADOn_cramerShoup_bitStringAD is 1CCA security with associated data in {0,1}* \
    (Definition 12.7, pp. 501–502, one challenge), the exercise's statement in the one-challenge \
    form that Theorem 12.1 lifts to many challenges (p. 502); indcca2On_cramerShoup is the 1CCA \
    form without associated data (Definition 12.2, p. 468, ad = []); \
    indcca2InterleavedOn_cramerShoup is CCA security with adaptively interleaved challenge and \
    decryption queries (Attack Game 12.1 and Definition 12.1, pp. 467–468), without associated \
    data; indcca2MultiOn_cramerShoup is its restriction to one batch of challenges. A decryption \
    query on a challenge ciphertext (with its associated data) is answered as a rejection, \
    where the source forbids it. The proof follows Theorem 12.9 for the hybrid scheme E_CS of \
    Section 12.5.3, which is not formalized. Asymptotic; no concrete bound is stated."

register_result "elgamal-strongly-unpredictable-ciphertexts" where
  title := "Multiplicative ElGamal, and hybrid ElGamal hashing the shared secret alone, have \
    strongly unpredictable ciphertexts"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "remark that ElGamal-based encryption meets the requirement (unnumbered)",
      locator := "Section 21.4.1, p. 872" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.stronglyUnpredictable_elGamalEncryptProb,
    Cslib.Crypto.PrimeOrderGroupFamily.stronglyUnpredictable_hybrid_hashedElGamal
  ]
  scope := "StronglyUnpredictable (Encryption/StronglyUnpredictable.lean) is the definition of \
    Section 21.4.1: one negligible ε such that at every n, for every public key word pk, \
    including malformed or adversarially chosen ones, every message m and every non-error \
    ciphertext c, Pr[E(pk, m) = c] ≤ ε(n). The book's error output is none; these schemes \
    never produce it. stronglyUnpredictable_iff_forall, in that module, shows that when the \
    key, message and ciphertext types are nonempty at each parameter, the single ε is \
    equivalent to negligibility along every sequence (pk, m, c). The schemes are the \
    library's ElGamal programs over a PrimeOrderGroupFamily with a deterministic group \
    schedule d, the group at n being d n: elGamalEncryptProb, the multiplicative ElGamal \
    scheme E_MEG of Exercise 11.5 (p. 459), for any message encoding; and hybridEncrypt \
    (hashedElGamalEncapsProb H d) encryptSym, the KEM–DEM form of the variant E′_EG of \
    Remark 11.1 (p. 446), which hashes w alone, for any hash H and any symmetric encryption \
    algorithm. E_EG itself, which hashes (v, w), is not an instance, although the argument does \
    not depend on the hash. Hypothesis: 1/q(d n) is negligible, a condition on the parameters \
    that CDH or DDH at the point-mass setup implies (CDH.negligible_inv_order and \
    DDH.negligible_expected_inv_order, DiffieHellman/Order.lean). Both schemes draw the \
    ephemeral exponent β with the fair-coin sampler sampleExp, and the first ciphertext \
    component β·g determines β mod q, so ciphertextHitBound_elGamalEncryptProb and \
    ciphertextHitBound_hybrid_hashedElGamal, in the same module, bound every hit probability by \
    1/q + 1/2^n. The collision bound of Section 21.9.6 (p. 897) is not part of this entry."

register_result "ddh-even-order-parity-attack" where
  title := "DDH does not hold in cyclic groups of even order"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Exercise 10.24, with the parity test of Section 16.1.3 (Lemmas 16.1–16.2)",
      locator := "Section 10.11, p. 431; Section 16.1.3, p. 687" }
  ]
  theorems := [
    Cslib.Crypto.CyclicGroupFamily.not_ddh_of_even_order,
    Cslib.Crypto.CyclicGroupFamily.isPPT_ddhParityDistinguisher
  ]
  scope := "CyclicGroupFamily.DDH setup is Attack Game 10.6 (p. 410) with the order not \
    required to be prime, as Exercise 10.24 specifies: group parameters d from any setup law, \
    uniform exponents in Z_q, and distinguishers that are uniform strict PPT on the encoding of \
    (1^n, d, a·g, b·g, w). On a prime-order family it is PrimeOrderGroupFamily.DDH \
    (ddh_toCyclicGroupFamily_iff). The distinguisher is the test of Section 16.1.3 (p. 687), \
    written additively: it accepts when (q/2)·w = 0 holds exactly when (q/2)·(a·g) = 0 or \
    (q/2)·(b·g) = 0, the parity comparison of Lemmas 16.1 and 16.2. It is deterministic and \
    certified uniform strict PPT on that encoding (isPPT_ddhParityDistinguisher). \
    not_ddh_of_even_order: if every group the setup law can produce has even order, DDH does \
    not hold. The proof gives the parity test advantage at least 1/2 at every n \
    (inv_le_advantage_ddhSmallFactorDistinguisher with the factor 2), and \
    ddhAdvantage_ddhParityDistinguisher (DiffieHellman/EvenOrder.lean) states that its \
    advantage is exactly 1/2 in every fixed cyclic group of even order, the exercise's 1/2. \
    The hypothesis can hold: not_ddh_residueGroups (CslibFrontierTests, \
    DiffieHellmanEvenOrder.lean) applies the theorem to a family of even-order groups. \
    Efficiency is polynomial time on encodings, not a count of group operations. The book's \
    remark that DDH fails in Z_p^* is proved only for one fixed group \
    (ddhAdvantage_units_ddhParityDistinguisher); no family of the groups Z_p^* is constructed."

register_result "ddh-small-prime-factor-attack" where
  title := "DDH does not hold when the group order has a polynomially small prime factor"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Exercise 16.2(a): the advantage bound and its asymptotic consequence",
      locator := "Section 16.7, p. 707" }
  ]
  theorems := [
    Cslib.Crypto.CyclicGroupFamily.not_ddh_of_polynomiallyBounded_minFac,
    Cslib.Crypto.CyclicGroupFamily.inv_le_advantage_ddhSmallFactorDistinguisher,
    Cslib.Crypto.CyclicGroupFamily.isPPT_ddhSmallFactorDistinguisher
  ]
  scope := "DDH over a CyclicGroupFamily, as in the entry for Exercise 10.24: Attack Game 10.6 \
    (p. 410) without the prime-order restriction, any setup law, and uniform strict PPT \
    distinguishers on encodings. ddhSmallFactorDistinguisher generalizes the parity test of \
    Section 16.1.3 from 2 to a prime factor l of q: it accepts when (q/l)·w = 0 holds exactly \
    when (q/l)·(a·g) = 0 or (q/l)·(b·g) = 0. It takes a factor selector and is certified \
    uniform strict PPT whenever the selector is polynomial time \
    (isPPT_ddhSmallFactorDistinguisher). inv_le_advantage_ddhSmallFactorDistinguisher: when the \
    selected factor is a prime divisor of q at most B for every group in the support of \
    setup n, the advantage at n is at least 1/B. not_ddh_of_polynomiallyBounded_minFac: if for \
    infinitely many n every group in the support has q > 1 with smallest prime factor at most \
    bound n, for a polynomially bounded bound, then DDH does not hold. This is the exercise's \
    conclusion that DDH is false when the smallest prime factor is small, with small read as \
    polynomially bounded. The proof's selector finds the greatest prime factor up to a \
    polynomial majorant C·(n + 1)^D of bound n, by bounded search with a primality test, where \
    the exercise uses the smallest; that factor can exceed bound n, so the proof's advantage \
    is at least 1/(C·(n + 1)^D). In one fixed group and \
    for a prime l dividing q, ddhAdvantage_ddhSmallFactorDistinguisher \
    (DiffieHellman/SmallFactor.lean) gives the exact advantage (3l − 2)(l − 1)/l³, at least 1/l \
    (inv_le_ddhAdvantage_ddhSmallFactorDistinguisher), the exercise's 'about 1/ℓ'. \
    Efficiency is polynomial time on encodings; the exercise's O(log q) group operations is not \
    proved as a count of group operations. Part (b) is not formalized."

register_result "rsa-close-prime-factoring" where
  title := "An RSA modulus whose prime factors differ by less than 2n^{1/4} is factored in \
    polynomial time"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Lemma 16.4 and the factoring method that follows it",
      locator := "Section 16.4.2.1, p. 699" }
  ]
  theorems := [
    Cslib.Crypto.abs_add_div_two_sub_sqrt_mul_lt_half,
    Cslib.Crypto.RSADesc.fermatFactor_eq,
    Cslib.Crypto.computableInPolyTime_fermatFactor
  ]
  scope := "Lemma 16.4, abs_add_div_two_sub_sqrt_mul_lt_half: for positive reals p and q with \
    |p − q| < 2(pq)^{1/4}, |(p + q)/2 − √(pq)| < 1/2, as printed with n = pq. The factoring \
    method: fermatFactor n sets A = ⌈√n⌉ (step 1) and solves p + q = 2A, pq = n for the \
    factors with factorOfTotient (step 2). RSADesc.fermatFactor_eq: for an RSA key description \
    (distinct primes p and q, modulus n = pq) with p ≠ 2 and q ≠ 2, the book's 'p and q are odd \
    primes', and |p − q| < 2n^{1/4}, the last bound of (16.11), fermatFactor n is \
    (max p q, min p q). computableInPolyTime_fermatFactor: fermatFactor runs in polynomial time \
    on binary naturals. It tries only A = ⌈√n⌉, as on p. 699, not the search over A of \
    Exercise 16.13; the name fermatFactor is the library's. The generalization to \
    |ap − bq| < n^{1/4} (Exercise 16.14, p. 710) is in Factoring/LinearRelation.lean and is not \
    part of this entry."

register_result "rsa-shared-prime-gcd" where
  title := "Distinct RSA moduli that share a prime factor are factored by their gcd"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "gcd attack on moduli that share a prime (unnumbered)",
      locator := "Section 16.4.2, p. 698" }
  ]
  theorems := [
    Cslib.Crypto.RSADesc.gcd_modulus_eq_of_p_eq
  ]
  scope := "For two RSA key descriptions with the same prime p and different second primes, \
    gcd(n₁, n₂) = p, which factors both moduli. The book's attacker computes gcd(n_i, n_j) for \
    the moduli of devices that generated the same p from a low-entropy seed; that key \
    generation is not modelled, and the shared prime is the first prime of both descriptions. \
    gcd_mul_mul_of_prime_ne, in the same module, is the identity on naturals. The gcd is \
    polynomial time on binary naturals by Turing.MultiTapeTM.ComputableInPolyTime.binary_gcd, \
    the library's certificate for Nat.gcd, in another module."

register_result "generic-group-dlog-lower-bound" where
  title := "A generic algorithm with T group-oracle queries finds a discrete logarithm with \
    probability at most ((3T + 2)²/2 + 1)/q"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 16.3", locator := "Section 16.3, pp. 693–695" }
  ]
  theorems := [
    Cslib.Crypto.GenericGroup.succProbability_dlogGame_le,
    Cslib.Crypto.GenericGroup.le_of_half_le_succProbability_dlogGame
  ]
  scope := "The generic group model as Boneh–Shoup state it (Section 16.3, p. 693): the oracle \
    holds a uniformly random injective labeling L : Z_q → S and answers a labeling query β \
    with L(β), and a group operation (ℓ₁, ℓ₂, κ₁, κ₂) with L(κ₁β₁ + κ₂β₂) when ℓ₁ = L(β₁) and \
    ℓ₂ = L(β₂), and with reject (none) otherwise (GroupOracleSpec, answer, runLabeled). S is \
    any finite type with an injection from Z_q, the book's |S| ≥ q, in place of a set of bit \
    strings; groups are written additively. dlogGame draws L and α uniformly, gives the \
    adversary L(1) and L(α) without charging it a query, and wins when the adversary outputs α: \
    Game 0 of the proof. Adversaries are randomized oracle programs, otherwise unbounded as on \
    p. 695, that make at most T labeling and group-operation queries on every path \
    (IsQueryBounded; private coins are free). succProbability_dlogGame_le: for prime q, the \
    success probability is at most ((3T + 2)²/2 + 1)/q, eq. (16.6). \
    le_of_half_le_succProbability_dlogGame: success probability at least 1/2 forces \
    q ≤ (3T + 2)² + 2, the remark on p. 695 that T must then be about √q/3 or more. \
    succProbability_dlogGame_le_choose, in the same module, is the sharper \
    ((3T + 2) choose 2 + 1)/q that the proof gives before rounding. No computational \
    assumption: a statement in the idealized model, not about any specific group."

register_result "generic-group-cdh-lower-bound" where
  title := "A generic algorithm with T group-oracle queries solves CDH with probability at most \
    ((3T + 4)²/2 + 2)/q"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 16.5(a)", locator := "Section 16.7, p. 708" }
  ]
  theorems := [
    Cslib.Crypto.GenericGroup.succProbability_cdhGame_le,
    Cslib.Crypto.GenericGroup.le_of_half_le_succProbability_cdhGame
  ]
  scope := "The generic group model of Section 16.3 (p. 693), with the oracle, labelings, finite \
    label type with |S| ≥ q, query budget and otherwise unbounded randomized adversaries of the \
    entry for Theorem 16.3. cdhGame draws L, α and β uniformly, gives the adversary L(1), L(α) \
    and L(β), and wins when the adversary outputs the label L(αβ). The exercise asks for a \
    lower bound, similar to Theorem 16.3, on the time to compute CDH with probability one half, \
    and prints no bound. succProbability_cdhGame_le: for prime q, the success probability is at \
    most ((3T + 4)²/2 + 2)/q; the proof's table holds two more linear forms than in \
    Theorem 16.3 (the challenge L(β) and the output label), and the guess term is 2/q because \
    XY agrees with a fixed linear form at no more than 2q − 1 of the q² points. \
    le_of_half_le_succProbability_cdhGame: success probability at least 1/2 forces \
    q ≤ (3T + 4)² + 4, so T must be about √q/3 or more. succProbability_cdhGame_le_choose, in \
    the same module, is a sharper bound, ((3T + 4) choose 2 + 2)/q. The bound is not claimed \
    for composite q. Part (b), interactive CDH, is not formalized."

register_result "hors-containment-free" where
  title := "The HORS subset map is a polynomial-time containment-free map into sets of size ℓ"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "the injective map P_hors into Sets[n, ℓ] (unnumbered)",
      locator := "Section 14.4, p. 593" }
  ]
  theorems := [
    Cslib.Crypto.OneTimeSignature.horsSet_containmentFree,
    Cslib.Crypto.OneTimeSignature.card_horsSet,
    Cslib.Crypto.OneTimeSignature.horsWord_polyTime
  ]
  scope := "ContainmentFree P is Definition 14.3 (p. 587): P(m) ⊄ P(m′) for distinct m and m′, \
    which implies that P is injective. Section 14.4 needs an injective, efficiently computable \
    P_hors : {0,1}^v → Sets[n, ℓ], says that such a map is containment free, and refers to \
    Exercise 14.3 (Section 14.9, pp. 607–608) for one whenever 2^v ≤ (n choose ℓ). horsSet n ℓ \
    sends a v-bit message to the positions, numbered from 0, of the true bits of \
    horsWord n ℓ m = unrankCombination n ℓ applied to the value of m read most significant bit \
    first. card_horsSet: when 2^v ≤ (n choose ℓ), every image has ℓ elements. \
    horsSet_containmentFree: under the same condition, horsSet n ℓ is containment free. \
    horsWord_polyTime: horsWord runs in time polynomial in n and ℓ, given in unary, and in the \
    message. The unranking is the library's unrankCombination, which takes the branches in the \
    opposite order to the loop printed in Exercise 14.3; that loop is not formalized, so the \
    entry claims the map of Section 14.4, not the exercise's algorithm. The HORS signature \
    scheme, its security and the Merkle-tree public key are not part of this entry."

register_result "prf-mac-suf-cma" where
  title := "A secure pseudorandom function is a strongly unforgeable MAC"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 6.2", locator := "Section 6.3, p. 224" }
  ]
  theorems := [
    Cslib.Crypto.PseudorandomFunction.sufCma_prfMAC,
    Cslib.Crypto.succProbability_sufCmaGame_prfMAC_le
  ]
  scope := "Let F be a PseudorandomFunction: n-bit keys, inputs and outputs, deterministic \
    polynomial-time evaluation, secure against adaptive uniform oracle-PPT tests, with queries \
    of another length answered by the empty word (Attack Game 4.2 and Definition 4.2, \
    pp. 132–133). This is Theorem 6.2's PRF over (K, X, Y) with K = X = Y = {0,1}^n, so \
    |Y| = 2^n is super-poly. The MAC proved secure is prfMAC, the deterministic MAC derived from \
    F in Section 6.3 (p. 223): a uniform n-bit key, the tag F(k, m) of an n-bit message, and \
    verification by recomputing the tag. It is a MACScheme, whose fields certify strict PPT key \
    generation and tagging, polynomial-time verification and correctness on n-bit messages. The \
    notion is SUFCMA (Attack Game 6.1 and Definition 6.2, pp. 218–219), against uniform strict \
    oracle-PPT forgers in the standard model: a forgery wins when it is a valid pair on an n-bit \
    message that the tagging oracle never returned. As in the source, tagging queries and the \
    forgery lie in the message space of n-bit words: the tagging oracle answers a query of \
    another length with the empty word, without tagging or recording it, and a candidate tag \
    that is not an n-bit word never verifies, so the notion is Definition 6.2 for prfMAC on \
    n-bit messages. The reduction macToPrfDistinguisher forwards each n-bit tagging query to \
    its PRF oracle, refuses the others itself, and is certified oracle PPT \
    (isOraclePPT_macToPrfDistinguisher). Asymptotic; succProbability_sufCmaGame_prfMAC_le, \
    in the same module, is the theorem's bound MACadv[A, I] ≤ PRFadv[B, F] + 1/2^n, with \
    1/2^n = 1/|Y|."

register_result "encrypt-then-mac-authenticated-encryption" where
  title := "Encrypt-then-MAC is authenticated encryption, many-time and one-time"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 9.2", locator := "Section 9.4.1, p. 367" }
  ]
  theorems := [
    Cslib.Crypto.ciphertextIntegrity_encryptThenMAC,
    Cslib.Crypto.authenticatedEncryption_encryptThenMAC,
    Cslib.Crypto.oneTimeCiphertextIntegrity_encryptThenMAC,
    Cslib.Crypto.oneTimeAuthenticatedEncryption_encryptThenMAC,
    Cslib.Crypto.succProbability_ciGame_encryptThenMAC_eq,
    Cslib.Crypto.succProbability_ciOneTimeGame_encryptThenMAC_eq
  ]
  scope := "Both sentences of Theorem 9.2 (proof pp. 367–368) for encryptThenMAC E M, the \
    encrypt-then-MAC cipher of Section 9.4.1 (p. 367): independent keys (ke, km) from the key \
    generators of E and M; a ciphertext is the framed pair (c, t) of c ← E(ke, m) and \
    t ← S(km, c); decryption rejects unless the word is a canonically framed pair whose first \
    part has msgLen n bits and V(km, c, t) accepts, and then outputs D(ke, c). E is any \
    SymmetricCipher (n-bit messages at parameter n, as in the authenticated-encryption-cca \
    entry) and M any MACScheme, under the hypothesis hctLen that E's ciphertexts of n-bit \
    messages have msgLen n bits: the source asks that I be defined over E's ciphertext space \
    C, and a MACScheme's message space at parameter n is the msgLen n-bit words. The \
    ciphertext space is the framed pairs whose first part has msgLen n bits and lies in \
    E.ctSpace n, with any word as tag: the source's C × T, a MACScheme declaring no tag \
    space. ciphertextIntegrity_encryptThenMAC and authenticatedEncryption_encryptThenMAC: if \
    E is CPA-secure (INDCPA, Attack Game 5.2 and Definition 5.2, pp. 181–182) and M is a \
    secure MAC (SUFCMA, Attack Game 6.1 and Definition 6.2, pp. 218–219, with tagging queries \
    and forgery in the message space), the cipher has ciphertext integrity (Attack Game 9.1 \
    and Definition 9.1, pp. 358–359) and is AE-secure (Definition 9.2, p. 359). The one-time \
    forms: if E is OneTimeINDCPA (Attack Game 5.2 answering one encryption query, standing \
    for the theorem's semantic security) and M is OneTimeSUFCMA (Attack Game 6.1 with one \
    tagging query, Section 7.6, p. 275, against efficient forgers), the cipher has one-time \
    ciphertext integrity and is 1AE-secure (Definitions 9.3–9.4, p. 360). Adversaries are \
    uniform strict oracle-PPT programs in the standard model, with the game conventions of the \
    authenticated-encryption-cca entry. succProbability_ciGame_encryptThenMAC_eq and its \
    one-time form are the theorem's CIadv[Aci, EEtM] = MACadv[Bmac, I], for the reductions \
    etmToMACForger and etmToOneTimeMACForger, which are certified oracle PPT and make no more \
    tagging queries than the adversary makes encryption queries \
    (isQueryBounded_etmToMACForger); advantage_cpaGame_encryptThenMAC_eq, in the same module, \
    is the theorem's CPA equality."

register_result "mac-then-encrypt-plaintext-integrity" where
  title := "MAC-then-encrypt has plaintext integrity"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 9.15(a), plaintext-integrity half",
      locator := "Section 9.13, p. 395" }
  ]
  theorems := [
    Cslib.Crypto.encForge_macThenEncrypt
  ]
  scope := "The plaintext-integrity half of Exercise 9.15(a), \"Show that MAC-then-Encrypt is \
    both CPA and PI secure\", for macThenEncrypt E M, the MAC-then-encrypt cipher of \
    Section 9.4.2 (p. 369): tag t ← S(km, m), encrypt the framed pair (m, t) under ke, and on \
    decryption reject unless the plaintext is a canonically framed pair whose first part has \
    n bits and V(km, m, t) accepts, then output m. M is any MACScheme on n-bit messages \
    (hmsgLen); E is any SymmetricCipher, run at parameter ptLen n so that it encrypts \
    ptLen n-bit words, under the hypothesis hpairLen that every framed pair of an n-bit \
    message and an honest tag has ptLen n bits: the source asks that E be defined over \
    M × T, and a SymmetricCipher's message space at parameter ptLen n is the ptLen n-bit \
    words. Plaintext integrity is EncForge, the ciphertext integrity game of Attack Game 9.1 \
    (pp. 358–359) won, as Exercise 9.15 defines, when the output decrypts to a message that \
    was never queried; encryption queries other than n-bit messages are answered with the \
    empty word. The hypothesis is that M is EUFCMA: fresh-message unforgeability with tagging \
    queries and forgery in the message space, which a secure MAC (SUFCMA, Definition 6.2, \
    pp. 218–219) implies (MACScheme.SUFCMA.eufCma). Nothing is assumed of E, so the \
    conclusion holds for every MAC-then-encrypt cipher built from a secure MAC. Adversaries \
    are uniform strict oracle-PPT programs in the standard model. The reduction \
    mteToMACForger is certified oracle PPT (isOraclePPT_mteToMACForger), and \
    succProbability_encForgeGame_macThenEncrypt_le, in the same module, is its concrete \
    bound."

register_result "authenticated-encryption-cca" where
  title := "Authenticated encryption implies chosen-ciphertext security, many-time and one-time"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 9.1", locator := "Section 9.2.3, p. 363" }
  ]
  theorems := [
    Cslib.Crypto.SymmetricCipher.AuthenticatedEncryption.indcca,
    Cslib.Crypto.SymmetricCipher.OneTimeAuthenticatedEncryption.oneTimeINDCCA
  ]
  scope := "Both sentences of Theorem 9.1 (proof pp. 363–365), for any SymmetricCipher: strict PPT \
    key generation and encryption, deterministic polynomial-time decryption returning a \
    message or a rejection, and correct decryption of encryptions of n-bit messages; the \
    source allows any message space, here messages have exactly n bits at parameter n. A \
    source cipher over (K, M, C) (Definition 2.10, p. 31) is encoded by choosing ctSpace n to \
    be the membership test of C and decryption to reject every word outside C, as the field \
    decrypt_eq_none_of_ctSpace_eq_false requires; Definition 2.10 also makes C efficiently \
    recognizable, which the proof does not use. The integrity games accept any fresh word as \
    a forgery, but a word outside C decrypts to a rejection and loses, so CiphertextIntegrity \
    is Attack Game 9.1 on C and the premise is the source's. The CCA games also answer \
    decryption queries outside C, with a rejection; the source's adversaries ask only words \
    of C, so the conclusion implies CCA security on C. AuthenticatedEncryption.indcca: an \
    AE-secure cipher (Definition 9.2, p. 359: CPA security, Attack Game 5.2 and \
    Definition 5.2, pp. 181–182, and ciphertext integrity, Attack Game 9.1 and Definition 9.1, \
    pp. 358–359) is CCA-secure (Attack Game 9.2 and Definition 9.5, p. 362). \
    OneTimeAuthenticatedEncryption.oneTimeINDCCA: a 1AE-secure cipher (Definitions 9.3–9.4, \
    p. 360) is 1CCA-secure (Definition 9.6, p. 363). Adversaries are uniform strict \
    oracle-PPT programs in the standard model, and the advantage is the two-experiment one of \
    Attack Game 9.2. An encryption query that is not a pair of n-bit messages is answered with \
    the empty word without encrypting; a decryption query on a ciphertext that the oracle \
    returned is answered as a rejection instead of being prohibited; the one-time games \
    answer only the first valid encryption query instead of restricting the adversary to \
    one. The reductions ccaToCPAAdversary and ccaToCIHiddenBitAdversary are certified oracle \
    PPT. Asymptotic; the concrete bound advantage_ccaGame_le_two_mul, in the same module, has \
    CI coefficient 2 · dyadicSize(Qd − 1), at most 4 Qd when Qd ≥ 1, in place of the 2 Qd of \
    (9.3), because the CI reduction draws its query index with fair coins; \
    guessingAdvantage_guessBit_ccaGame_le_two_mul states (9.4) with 2 Qd in place of Qd."

register_result "prepend-key-prf-random-oracle" where
  title := "Prepending the key to a random oracle gives a PRF with advantage at most Q_ro/|K| \
    for every nonempty finite key space, and a secure PRF when 1/|K| is negligible in the \
    security parameter"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 8.9",
      locator := "Section 8.10.2, p. 329 (Attack Game 8.4 and Definition 8.5, p. 329)" }
  ]
  theorems := [
    Cslib.Crypto.PRF.roAdvantage_prependKey_le,
    Cslib.Crypto.PRF.negligible_roAdvantage_prependKey,
    Cslib.Crypto.PRF.roAdvantage_prependKey_keyAppend_le,
    Cslib.Crypto.PRF.negligible_roAdvantage_prependKey_keyAppend
  ]
  scope := "Attack Game 8.4 for finite types Key, X, M and T: both experiments sample a uniform \
    oracle table O : M → T; Experiment 0 samples a uniform key and answers each F-query x with \
    F_pre(k, x) = O(encode(k, x)), Experiment 1 answers with a uniform f : X → T, and both \
    answer oracle queries with O. The advantage is |Pr[W₀] − Pr[W₁]|. Adversaries are adaptive \
    programs with private coins that make at most Q oracle queries on every path, with no bound \
    on F-queries or running time; the book notes that the theorem constrains only the number of \
    oracle queries. roAdvantage_prependKey_le: for every nonempty finite key set and any pairing \
    encode : Key → X → M that is injective in the pair (in place of k ‖ x), the advantage is at \
    most Q/|Key|; this finite bound needs no growth of the key space. \
    roAdvantage_prependKey_keyAppend_le is the book's instance K = {0,1}^κ and \
    X = {0,1}^(≤L), with bound Q/2^κ; there M is exactly the words of length at most κ + L, \
    while the book allows M to contain more, which the general theorem covers for any finite \
    M. negligible_roAdvantage_prependKey and negligible_roAdvantage_prependKey_keyAppend: under \
    the key-growth condition that 1/|Key n| is negligible (for bit strings, keys of at least n \
    bits), the book's 'if K is large', every family of \
    adversaries with polynomially many oracle queries has negligible advantage; efficient \
    adversaries are such families, so this gives Definition 8.5. The proof is not the book's \
    and does not assume that F-queries are distinct. Not formalized: the insecurity of F_pre \
    for a Merkle–Damgård hash (p. 329) and Section 8.10.3."

register_result "merkle-damgard-collision-resistance" where
  title := "The Merkle–Damgård hash of a collision-resistant compression function is collision \
    resistant"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 8.3", locator := "Section 8.4, p. 297" }
  ]
  theorems := [
    Cslib.Crypto.CompressionFamily.collisionResistant_lengthStrengthenedMD,
    Cslib.Crypto.CompressionFamily.hashFamily_lengthStrengthenedMD
  ]
  scope := "Let h be a CompressionFamily: deterministic polynomial time, mapping 2n-bit inputs \
    under a uniform n-bit key to n-bit digests, and collision resistant on 2n-bit inputs \
    against uniform strict PPT finders (Attack Game 8.1 and Definitions 8.1–8.2, pp. 290–291, \
    with the key as the system parameter, as footnote 1 on p. 290 allows). This is \
    Theorem 8.3's h over (X × Y, X) with X = Y = {0,1}^n, the chaining value and the block read \
    as one 2n-bit word. lengthStrengthenedMD h is the hash H_MD of Section 8.4 and Figure 8.5 \
    (pp. 295–297) with IV = 0^n and padding block PB = 1 ‖ 0^k ‖ ⟨s⟩, whose length field ⟨s⟩ \
    has n/2 bits (the book's is a fixed-length field, typically 64 bits) and counts the blocks \
    of the padded message, the count the proof on p. 297 uses (p. 296 says the blocks of M). \
    collisionResistant_lengthStrengthenedMD: H_MD is collision resistant on all bit strings \
    against uniform strict PPT finders, in place of the source's {0,1}^{≤L} for a poly-bounded \
    L. A strict PPT finder outputs polynomially long messages, whose block counts fit in the \
    length field for all large n, so this covers every poly-bounded L at once. \
    hashFamily_lengthStrengthenedMD adds polynomial-time evaluation and n-bit digests, \
    packaging H_MD as a HashFamily. The proof's B is lengthStrengthenedWrapper, certified \
    strict PPT (isPPT_lengthStrengthenedWrapper). Asymptotic; \
    succProbability_collisionGame_lengthStrengthenedMD_eq, in the same module, is the \
    theorem's CRadv[A, H_MD] = CRadv[B, h] on any message domain whose padded block counts \
    are below 2^(n/2). The one-bit-per-block hash merkleDamgard of MerkleDamgard.lean is not \
    part of this entry."

register_result "davies-meyer-ideal-cipher-collision-resistance" where
  title := "Davies–Meyer is collision resistant in the ideal cipher model: a deterministic \
    adaptive finder making Q queries finds a collision with probability at most \
    (Q + 1)(Q + 2)/|X|"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 8.4",
      locator := "Section 8.5.3, p. 302 (the construction: Section 8.5.2, p. 300)" }
  ]
  theorems := [
    Cslib.IdealCipher.daviesMeyer_collisionGame_mul_le,
    Cslib.IdealCipher.daviesMeyer_collisionGame_le
  ]
  scope := "The ideal cipher is a family of independent uniform permutations Π_k of a finite \
    nonempty block set X, one for each key of a finite key set K. A CollisionFinder is an \
    oracle program (OracleComp) over the cipher's forward replies Π_k(a) and inverse replies \
    Π_k⁻¹(b) that outputs two inputs. It is adaptive but has no private sampling operation, so \
    the declarations quantify over deterministic adaptive finders; IsQueryBounded A Q bounds \
    its queries of both kinds by Q on every path, with no bound on running time. The book's \
    adversary may be randomized; averaging the bound over its coins would extend it, but no \
    private-coin version is proved. collisionGame samples the cipher, runs the finder, and \
    evaluates the compression function on its two outputs directly with the sampled \
    permutations, accepting distinct inputs with equal digests; these two digest evaluations \
    are not queries of the finder. The proof's program daviesMeyerCollisionProgram instead \
    appends two forward queries on the outputs, which gives Q + 2 queries (the book's \
    'reasonable' adversary with q′ = q + 2). daviesMeyer Π (k, x) = Π_k(x) + x is the book's \
    h_DM(x, y) = E(y, x) ⊕ x with its arguments swapped, which is a bijection of the input \
    space, for any group structure + on X: XOR on {0,1}^n, and also modular addition as in \
    SHA256 (p. 304). daviesMeyer_collisionGame_mul_le is the book's bound (Q + 2)(Q + 1)/|X|, \
    and daviesMeyer_collisionGame_le is the same bound written 2·C(Q + 2, 2)/|X|."

register_result "davies-meyer-insecure-variants" where
  title := "The Davies–Meyer variants h₄ and h₅ have two-query collision finders that always \
    succeed in the ideal cipher model"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 8.11, in the ideal cipher model",
      locator := "Section 8.14, p. 349 (the variants h₄ and h₅: Section 8.5.2, p. 301)" }
  ]
  theorems := [
    Cslib.IdealCipher.keyMaskedAdversary_wins,
    Cslib.IdealCipher.keyMaskedInputAdversary_wins,
    Cslib.IdealCipher.exists_collisionFinder_keyMasked,
    Cslib.IdealCipher.exists_collisionFinder_keyMaskedInput
  ]
  scope := "Keys and blocks are the same finite set X with a group structure + (XOR on {0,1}^n). \
    keyMasked Π (k, x) = Π_k(x) + k is h₄(x, y) = E(y, x) ⊕ y with its arguments swapped, and \
    keyMaskedInput Π (k, x) = Π_k(k + x) + k is h₅(x, y) = E(x, x ⊕ y) ⊕ x. Two kinds of result \
    exist. For any fixed family of permutations F, which covers a concrete block cipher, \
    BlockCipherCompression.keyMasked_collision and keyMaskedInput_collision \
    (Hash/BlockCipherCompression.lean, not listed, since an entry has one defining module) are \
    pointwise algebraic facts: for keys k₁ ≠ k₂ and any target y, the inputs built from \
    F_k₁⁻¹(y − k₁) and F_k₂⁻¹(y − k₂) are distinct and collide. They make no cost claim. The \
    listed theorems are the cost claim in the ideal cipher game of \
    davies-meyer-ideal-cipher-collision-resistance: keyMaskedAdversary and \
    keyMaskedInputAdversary make the two inverse queries Π_k₁⁻¹(y − k₁) and Π_k₂⁻¹(y − k₂) and \
    output those inputs; they win collisionGame with probability exactly 1 \
    (keyMaskedAdversary_wins, keyMaskedInputAdversary_wins) with at most 2 queries \
    (isQueryBounded_keyMaskedAdversary and isQueryBounded_keyMaskedInputAdversary, in the same \
    module). The exists_ forms state this for every X with at least two elements. The book's \
    'constant time' (p. 301) is the count of two queries here; no running time, of the finder \
    or of a concrete cipher's inverse, is claimed. This exercise is kept separate from \
    Theorem 8.4."

register_result "second-preimage-counting-and-inversion" where
  title := "At most a 1/s fraction of inputs lack a second preimage, and inverting is at most \
    twice as easy as finding second preimages, up to 1/s"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 8.23(a) and the bound (8.22) of 8.23(b)",
      locator := "Section 8.14, pp. 352–353; Definition 8.6, Section 8.11.1, p. 336" }
  ]
  theorems := [
    Cslib.Crypto.card_not_hasSecondPreimage_div_le,
    Cslib.Crypto.succProbability_inversionExperiment_uniform_le_two_mul_add_div,
    Cslib.Crypto.succProbability_inversionExperiment_uniform_le_add_card_div
  ]
  scope := "For any function H : M → T between finite types, M nonempty, and any s > 0 with \
    s·|T| ≤ |M| (the book assumes s > 1). card_not_hasSecondPreimage_div_le (8.23(a)): the \
    inputs m with no m′ ≠ m such that H(m′) = H(m) form at most a 1/s fraction of M. The \
    experiments are those of Definition 8.6: inversionExperiment draws m uniformly from M, gives \
    H(m) to the inverter and accepts any preimage; secondPreimageExperiment gives m to the \
    finder and accepts m′ ≠ m with H(m′) = H(m). For every randomized inverter A : T → PMF M \
    and the finder B(m) = A(H(m)) of the exercise's hint, \
    succProbability_inversionExperiment_uniform_le_two_mul_add_div is (8.22), \
    OWadv[A, H] ≤ 2·SPRadv[B, H] + 1/s, and \
    succProbability_inversionExperiment_uniform_le_add_card_div is the sharper \
    OWadv[A, H] ≤ SPRadv[B, H] + |T|/|M|, from which (8.22) follows. These are concrete bounds \
    for every A, with no cost model; B calls A once. The asymptotic part of 8.23(b), that \
    second-preimage resistance implies one-wayness when s is super-poly, is entry \
    second-preimage-resistance-implies-one-way, and 8.23(c) is entry \
    second-preimage-resistant-not-one-way; 8.23(d) is not part of this entry."

register_result "second-preimage-resistance-implies-one-way" where
  title := "A second-preimage resistant function that compresses by a super-polynomial factor is \
    one-way"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Equation (8.17), second implication, and Exercise 8.23(b)",
      locator := "Section 8.11.1, p. 337; Section 8.14, pp. 352–353" }
  ]
  theorems := [
    Cslib.Crypto.SecondPreimageResistantOn.oneWayOn_of_outputLength
  ]
  scope := "H is one function on bit strings, evaluated in deterministic polynomial time, that \
    maps n-bit inputs to outLen(n)-bit digests. Hypotheses: SecondPreimageResistantOn H valid \
    and 2^outLen(n) / 2^n negligible. Conclusion: OneWayOn H valid, on the same answer domain. \
    At valid n w = decide (w.length = n) both are Definition 8.6 (Section 8.11.1, p. 336) on \
    M = {0,1}^n and T = {0,1}^outLen(n), with a uniform n-bit challenge and uniform strict PPT \
    adversaries given n in unary; a wider valid strengthens both. The compression factor \
    s(n) = |M| / |T| = 2^n / 2^outLen(n) is super-poly exactly when 1/s(n) is negligible; the \
    source assumes |M| ≥ s·|T|, and here s is that ratio. The proof's B is \
    inverterToSecondPreimage, which gives A the image of its challenge and returns A's answer, \
    as in the exercise's hint; it is certified strict PPT (isPPT_inverterToSecondPreimage). \
    Asymptotic; succProbability_inversionGameOn_le_secondPreimageGameOn_add, in the same \
    module, is the bound OWadv[A, H] ≤ SPRadv[B, H] + 2^outLen(n) / 2^n, which implies (8.22), \
    OWadv[A, H] ≤ 2·SPRadv[B, H] + 1/s; the finite form of (8.22) is entry \
    second-preimage-counting-and-inversion."

register_result "one-way-not-second-preimage-resistant" where
  title := "Ignoring one input bit keeps a function one-way but makes second preimages easy"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "a one-way h′(m, b) := h(m) that is not 2nd-preimage resistant",
      locator := "Section 8.11.1, p. 337" }
  ]
  theorems := [
    Cslib.Crypto.OneWayOn.ignoreHeadBit,
    Cslib.Crypto.not_secondPreimageResistantOn_ignoreHeadBit
  ]
  scope := "h is one function on bit strings, evaluated in deterministic polynomial time, and h′ \
    is ignoreHeadBit h, with h′(b :: m) = h(m): the source's h′(m, b) := h(m), with the extra \
    bit first. OneWayOn.ignoreHeadBit: if OneWayOn h valid, then OneWayOn h′ valid, for an \
    answer domain whose words at length n + 1 lose their head bit into words of the domain at \
    length n. At valid n w = decide (w.length = n) this is Definition 8.6 (Section 8.11.1, \
    p. 336) for h on M = {0,1}^n and for h′ on M × {0,1} = {0,1}^(n+1), with uniform \
    challenges and uniform strict PPT inverters given the input length in unary, so h′ at \
    length n + 1 corresponds to h at length n. The source says only that h′ is clearly \
    one-way; the reduction here is ignoreHeadBitInverter, which runs the inverter for h′ at \
    length n + 1 and returns the tail of its answer, certified strict PPT \
    (isPPT_ignoreHeadBitInverter). not_secondPreimageResistantOn_ignoreHeadBit: for every h, \
    h′ is not SecondPreimageResistantOn h′ valid for any valid that, for all large n, admits \
    every n-bit word with its head bit flipped, as {0,1}^n does. The finder flipHeadBit answers \
    the challenge b :: m with (1 − b) :: m, the source's (m, 1 − b), and wins with \
    probability 1."

register_result "second-preimage-resistant-not-one-way" where
  title := "At a bounded compression factor, a second-preimage resistant function need not be \
    one-way"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 8.23(c)", locator := "Section 8.14, p. 353" }
  ]
  theorems := [
    Cslib.Crypto.SecondPreimageResistantOn.plantEasyBranch,
    Cslib.Crypto.not_oneWayOn_plantEasyBranch
  ]
  scope := "For a function H on bit strings, evaluated in deterministic polynomial time, and \
    k : ℕ, H′ = plantEasyBranch k H maps w to true :: (w without its first k bits) when those k \
    bits are all false, and to false :: H(w) otherwise. \
    SecondPreimageResistantOn.plantEasyBranch: if SecondPreimageResistantOn H valid, then \
    SecondPreimageResistantOn H′ valid, on the same answer domain. not_oneWayOn_plantEasyBranch: \
    for every H, H′ is not OneWayOn H′ valid for any valid that contains every n-bit word; \
    plantEasyBranchInverter k, certified strict PPT (isPPT_plantEasyBranchInverter), answers \
    with k false bits followed by the tail of its challenge and inverts with probability at \
    least (1/2)^k at every length n ≥ k. At valid n w = decide (w.length = n) both notions are \
    Definition 8.6 (Section 8.11.1, p. 336) on M = {0,1}^n, with uniform n-bit challenges and \
    uniform strict PPT adversaries given n in unary. The exercise takes M := T × {1, …, 2s} \
    and T′ := T × {0,1}: when H maps n-bit inputs to (n − k)-bit digests, 2s = 2^k, and H′ maps \
    them to (n − k + 1)-bit digests (length_plantEasyBranch, same module), so H′ has \
    compression ratio s = 2^(k−1), with s = 2 at k = 2. Only compression factors that are \
    powers of two are covered. The two theorems hold for every H; the digest length only fixes \
    the compression ratio."

register_result "xor-tcr-from-second-preimage" where
  title := "Masking the input with the key turns a second-preimage-resistant hash into a target \
    collision resistant one"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 8.12", locator := "Section 8.11.3, p. 338" }
  ]
  theorems := [
    Cslib.Crypto.SecondPreimageResistantOn.targetCollisionResistantOn_xorTargetHash
  ]
  scope := "The keyed hash H_tcr(k, m) = H(k ⊕ m) of equation (8.18) (p. 338), as xorTargetHash, \
    with keys and messages of n bits: the source's M is taken to be {0,1}^n, with ⊕ the bitwise \
    XOR. H is one unkeyed function on bit strings, without a system parameter, evaluated in \
    deterministic polynomial time. Hypothesis: SecondPreimageResistantOn H valid for a validity \
    predicate that admits every n-bit word for all large n. At valid = validFixedLengthInput it \
    is Definition 8.6 (p. 336) on M = {0,1}^n, with a uniform n-bit challenge and uniform \
    strict PPT finders, the source's assumption; wider predicates give stronger assumptions. \
    Conclusion: TargetCollisionResistantOn for xorTargetHash H on n-bit messages (Attack \
    Game 8.5 and Definition 8.7, pp. 337–338) against uniform strict PPT two-stage adversaries, \
    which commit to m₀ before a uniform n-bit key is drawn. The proof's B is \
    xorTargetToSecondPreimage, certified strict PPT (isPPT_xorTargetToSecondPreimage). \
    Asymptotic; succProbability_targetCollisionGame_xorTargetHash_le, in the same module, is \
    the theorem's bound TCRadv[A, H_tcr] ≤ SPRadv[B, H]."

register_result "repeated-one-way" where
  title := "A function that is one-way on its domain stays hard to invert when polynomially many \
    instances are published and any others may be revealed"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Lemma 13.5",
      locator := "Section 13.4.1, Attack Game 13.3 and Lemma 13.5, pp. 539–540" }
  ]
  theorems := [
    Cslib.Crypto.OneWayOn.repeatedInversion_negligible
  ]
  scope := "f is one function on bit strings, evaluated in deterministic polynomial time. \
    Hypothesis: OneWayOn f valid for an answer domain valid that contains every n-bit word. At \
    valid n w = decide (w.length = n) it is Definition 8.6 (Section 8.11.1, p. 336) on \
    X = {0,1}^n, the lemma's standard one-way problem, with a uniform n-bit challenge and \
    uniform strict PPT inverters given n in unary; a wider valid gives a stronger premise and a \
    game that accepts more answers. Conclusion: for every number of instances t(n) computable \
    in polynomial time from unary n, every uniform strict oracle-PPT adversary has negligible \
    success in repeatedInversionGameOn f valid t, Attack Game 13.3 with x_1, …, x_t uniform \
    n-bit words: the adversary receives n in unary and the framed list (y_1, …, y_t), a reveal \
    query for slot j is answered with x_j, and the adversary wins with (ν, x) when it never \
    revealed ν, valid n x and f(x) = y_ν. The source's t is a positive integer parameter; here \
    it is a function of n, computable in polynomial time because the uniform reduction \
    computes it, and t(n) = 0 is allowed, where the game is lost. Slots are 0-based and named \
    by the length of the query word; a reveal outside 0, …, t(n) − 1 is answered with the empty \
    word, and a claim outside it loses. The proof's B is repeatedInverter, certified strict PPT \
    (isPPT_repeatedInverter); it forwards A's claimed preimage unchanged, and draws its guess ω \
    with fair coins from the dyadic range dyadicSize(t(n)) = 2^(⌊log₂ t(n)⌋ + 1) instead of \
    uniformly from 1, …, t, failing when ω ≥ t(n). Asymptotic; \
    succProbability_repeatedInversionGameOn_le, in the same module, is the bound (13.6) with \
    dyadicSize(t(n)) ≤ 2·t(n) in place of t: rOWadv[A, f, t] ≤ dyadicSize(t(n))·OWadv[B, f]."

register_result "tcr-hash-and-sign-signature" where
  title := "Signing a fresh target collision resistant hash key with the message digest extends a \
    secure signature to messages of any length"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 13.2", locator := "Section 13.2.1, p. 534" }
  ]
  theorems := [
    Cslib.Crypto.SignatureScheme.EUFCMA.eufCMA_wordScheme
  ]
  scope := "The derived scheme S′ of construction (13.2) (p. 533), as TCRSignature.wordScheme S \
    H: to sign m, sample a uniform H.keyLen n-bit key r, sign the pair (r, H(r, m)) under S and \
    output (r, σ), where the source outputs (σ, r); to verify, check that r has H.keyLen n bits \
    and that σ verifies on (r, H(r, m)) under S. Hypotheses: S.EUFCMA, Attack Game 13.1 and \
    Definition 13.2 (pp. 529–530) for a SignatureScheme, whose message space at security \
    parameter p is the p-bit words, with signing queries and forgeries in that space; and \
    H.TargetCollisionResistant, Attack Game 8.5 and Definition 8.7 (pp. 337–338) with every \
    word a message, uniform H.keyLen n-bit keys and H.digestLen n-bit digests. The source's S \
    signs the pairs of K_H × T at the same security parameter. Here, at parameter n, S runs at \
    the parameter otsParam H n, injective, computable in polynomial time and above \
    H.keyLen n + H.digestLen n, on the otsParam H n-bit word of r, then H(r, m), then zero \
    padding. So the premise is S's security on every otsParam H n-bit word, which includes the \
    encoded pairs, and the bound at n uses the advantage against S at otsParam H n, negligible \
    in n since otsParam H n ≥ n. The keys of S′ carry n. Conclusion: WordSignatureScheme.EUFCMA \
    for S′, Attack Game 13.1 with every word a message. The messages of H and of S′ are all \
    bit strings, which is security on every message space of polynomially bounded word length \
    at once. Forgers are uniform strict oracle-PPT machines and target-collision adversaries \
    uniform strict PPT two-stage machines. The proof's B_S is manyTimeForger and its B_H is \
    tcrMultiAdversary, both certified (isOraclePPT_manyTimeForger, isPPT_tcrMultiAdversary). \
    Asymptotic; exists_reduction_wordScheme_eufCmaGame_le, in the same module, is the \
    theorem's bound SIGadv[A, S′] ≤ SIGadv[B_S, S] + Q · TCRadv[B_H, H], with the term for S \
    at otsParam H n and a polynomially bounded loss in place of Q. The one-time form over a \
    one-time S (indexedEUFCMA_tcrSignature) is a step, not part of this entry."

register_result "rsa-common-root-shamir-trick" where
  title := "Shamir's trick: for a unit w modulo n with w^e ≡ y^f and coprime natural exponents \
    e and f, an e-th root of y in polynomial time"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 10.6, natural-exponent case",
      locator := "Section 10.6.2, p. 416" }
  ]
  theorems := [
    Cslib.Crypto.commonRoot_pow_modEq_right,
    Cslib.Crypto.commonRoot_coprime,
    Cslib.Crypto.commonRoot_lt,
    Cslib.Crypto.computableInPolyTime_commonRoot
  ]
  scope := "commonRoot n e f w y returns y mod n when f = 0, w mod n when f = 1, and otherwise \
    y^s (w⁻¹)^t mod n with s = e⁻¹ mod f and t = (es − 1)/f, so that es − ft = 1; the book \
    finds es + ft = 1 by the extended Euclidean algorithm and outputs y^s w^t. For 0 < n, \
    coprime e and f, w coprime to n and w^e ≡ y^f (mod n), the output x satisfies \
    x^e ≡ y (mod n) (commonRoot_pow_modEq_right) and x < n (commonRoot_lt); if y is also \
    coprime to n, then so is x (commonRoot_coprime), the book's x ∈ Z_n^*. commonRoot is \
    computable in polynomial time on binary natural numbers, with no condition on its inputs \
    (computableInPolyTime_commonRoot). Deviations: the book's e and f are integers, and here \
    they are natural numbers, so negative exponents are not covered; w and y are natural \
    numbers, not necessarily below n, and the root congruence needs only w coprime to n. The \
    unit hypothesis on w cannot be dropped: modulo 4, w = y = 2, e = 2 and f = 3 give \
    w^e ≡ y^f ≡ 0 with coprime exponents, but 2 has no square root modulo 4. \
    commonRoot_pow_modEq_left, in the same module, also gives x^f ≡ w (mod n), which the \
    theorem does not state. Deterministic; no assumption."

register_result "rsa-hash-collision-resistance" where
  title := "The RSA hash a^e y^b is collision resistant under the RSA assumption"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 10.7",
      locator := "Section 10.6.2, pp. 416–417" }
  ]
  theorems := [
    Cslib.Crypto.RSAOneWay.collisionResistantForOn_rsaHash
  ]
  scope := "Hypotheses: RSAOneWay gen, the RSA assumption (Attack Game 10.3 and Definition 10.5, \
    pp. 404–405) for a key law gen on RSADesc with a uniform challenge in Z_N, and that the \
    exponent e is prime for every key in the support of gen n, for all large n. The source \
    fixes one prime e and draws keys with RSAGen(ℓ, e); here gen is any law, which need not be \
    efficiently samplable, and the assumption is Boneh–Shoup's when gen is their RSAGen(ℓ, e) \
    for a prime e. Conclusion: H_rsa(a, b) = a^e y^b mod N (rsaHash, p. 415), keyed by (N, e, y) \
    with y uniform among the units modulo N (rsaHashSetup), is collision resistant \
    (CollisionResistantForOn: Attack Game 8.1 and Definitions 8.1–8.2, pp. 290–291) on its \
    domain Z_N^* × I_e against uniform strict PPT finders given 1^n and the key. Messages are \
    words: validRSAHashInput accepts the canonical encodings of pairs (a, b) with a < N coprime \
    to N and b < e, so distinct valid words are distinct pairs; digests are natural numbers \
    below N. The proof's B′ is rsaHashToRSA, certified strict PPT (isPPT_rsaHashToRSA), and \
    Theorem 10.5 (RSAOneWay.rsaUnitOneWay) passes from the unit-preimage game to the RSA game; \
    RSAUnitOneWay.collisionResistantForOn_rsaHash, in the same module, states the conclusion \
    from that variant assumption. Hash evaluation and the domain test are polynomial time \
    (computableInPolyTime_rsaHash, computableInPolyTime_validRSAHashInput). Asymptotic; \
    succProbability_collisionGameFor_rsaHash_le_rsaInversionGame, in the same module, is the \
    bound (10.3), CRadv[A, H_rsa] ≤ RSAadv[B, ℓ, e]."

register_result "rsa-crt-fault-attack" where
  title := "RSA-CRT inversion is correct for odd primes, and a fault in its mod-p half reveals \
    q = gcd(σ^e − h, n)"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "RSA-CRT inversion and the fault-injection attack on it (unnumbered)",
      locator := "Section 16.4.3, pp. 701–702" }
  ]
  theorems := [
    Cslib.Crypto.RSADesc.invert_crtKey,
    Cslib.Crypto.RSADesc.gcd_val_pow_sub_combine_eq_q,
    Cslib.Crypto.computableInPolyTime_crtKey_invert,
    Cslib.Crypto.computableInPolyTime_gcd_val_pow_sub
  ]
  scope := "For an RSA key RSADesc: distinct primes p and q, n = pq, and e·d ≡ 1 modulo \
    (p − 1)(q − 1). The RSA-CRT key is (p, q, d_p, d_q, q_inv) with d_p = d mod (p − 1), \
    d_q = d mod (q − 1) and q_inv = q⁻¹ mod p, computed by the extended Euclidean algorithm \
    (crtQInv); inversion is the book's steps 1–3, recombining as \
    x_q + (q_inv·(x_p − x_q) mod p)·q. invert_crtKey: for p ≠ 2 and q ≠ 2, RSA-CRT inversion \
    equals y^d mod n for every natural number y. The book's ordering p > q is not needed, and \
    oddness is: RSADesc admits p = 2, where d_p = 0 and step 1 is wrong on even y. \
    gcd_val_pow_sub_combine_eq_q: if x_q ≡ h^d (mod q) and x_p ≢ h^d (mod p), the recombined \
    output σ satisfies gcd(σ^e − h, n) = q, where σ^e − h is computed in Z_n and read as an \
    integer in [0, n), as on p. 702; h is any natural number in place of H(m), and q_inv is \
    any inverse of q modulo p. computableInPolyTime_crtKey_invert and \
    computableInPolyTime_gcd_val_pow_sub: RSA-CRT inversion and the gcd step are computable in \
    polynomial time on binary natural numbers from polynomial-time components, so q is found in \
    polynomial time from n, e, h and the faulty output. The fault is a hypothesis on x_p, not a \
    model of fault injection, and nothing is stated about an adversary in a security game. Not \
    formalized: the four-fold speed-up and RSA-CRT as the signer of FDH-RSA."

register_result "blinded-cdh-hard" where
  title := "The blinded Diffie–Hellman problem of protocol PAKE₂ is hard under CDH"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Lemma 21.7", locator := "Section 21.11.5, p. 910" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.CDH.negligible_blindedCDHGame
  ]
  scope := "Over a PrimeOrderGroupFamily with group parameters drawn from a setup law, under the \
    CDH assumption F.CDH setup (Attack Game 10.5 and Definition 10.7, pp. 409–410); the setup \
    law need not be efficiently samplable, and the assumption is Boneh–Shoup's when it is. \
    Given uniform a, b, u, v in the group, the adversary must output γ ∈ Z_q and \
    w = [u / a^γ, v / b^γ], written additively as blindedDH. The book names neither the problem \
    nor the game; blindedCDHGame is the library's name. Adversaries return a typed exponent and \
    group element, as in the source, and are uniform strict PPT on their encodings \
    (BlindedCDHAdversary.IsPPT), the convention of CDH. Conclusion: every such adversary wins \
    blindedCDHGame with negligible probability. The book's reduction blindedCDHToCDHAdversary \
    is certified strict PPT (isPPT_blindedCDHToCDHAdversary) and draws its two blinding \
    exponents with the fair-coin sampler sampleExp, each within 1/2^n of uniform, so \
    advantage_blindedCDHGame_cdhGame_le, in the same module, bounds the gap to the CDH game of \
    the reduction by 2/2^n. The PAKE₂ protocol and its random-oracle analysis are not \
    formalized."

register_result "two-point-blinded-cdh-hard" where
  title := "The two-point blinded Diffie–Hellman problem of protocol PAKE₂ is hard under CDH"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Lemma 21.8", locator := "Section 21.11.5, p. 911" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.CDH.negligible_blindedCDHPairGame
  ]
  scope := "Over a PrimeOrderGroupFamily with group parameters drawn from a setup law, under the \
    CDH assumption F.CDH setup (Attack Game 10.5 and Definition 10.7, pp. 409–410); the setup \
    law need not be efficiently samplable, and the assumption is Boneh–Shoup's when it is. \
    Given uniform a, b, u in the group, the adversary must output γ₁ ≠ γ₂ in Z_q, an element v \
    and wᵢ = [u / a^γᵢ, v / b^γᵢ] for i = 1, 2, written additively with blindedDH. The book \
    names neither the problem nor the game; blindedCDHPairGame is the library's name. \
    Adversaries return typed exponents and group elements, as in the source, and are uniform \
    strict PPT on their encodings (BlindedCDHPairAdversary.IsPPT), the convention of CDH. \
    Conclusion: every such adversary wins blindedCDHPairGame with negligible probability. The \
    book's reduction blindedCDHPairToCDHAdversary is certified strict PPT \
    (isPPT_blindedCDHPairToCDHAdversary) and draws its blinding exponent with sampleExp, within \
    1/2^n of uniform, so succProbability_blindedCDHPairGame_le, in the same module, bounds the \
    success probability by the reduction's CDH success plus 1/2^n. The PAKE₂ protocol and its \
    random-oracle analysis are not formalized."

register_result "kem-dem-hybrid-correctness" where
  title := "KEM–DEM hybrid encryption is correct"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 11.9(a)",
      locator := "Section 11.8, pp. 460–461" }
  ]
  theorems := [
    Cslib.Crypto.Encryption.hybridDecrypt_hybridEncrypt
  ]
  scope := "The hybrid scheme of the exercise (p. 461): hybridEncrypt encaps encryptSym draws \
    (k, c_kem) ← encaps n pk and c ← encryptSym n k m and outputs the framed pair (c_kem, c); \
    hybridDecrypt decaps decryptSym rejects a word that is not such a pair, then decapsulates \
    and decrypts, propagating either rejection. The theorem fixes n, pk, sk and a message m. \
    It assumes that decapsulation under sk recovers the key of every encapsulation in the \
    support of encaps n pk, the KEM correctness requirement of p. 460 at that key pair, and \
    that the DEM decrypts each of its ciphertexts of m under every key so encapsulated, cipher \
    correctness (Definition 2.10, p. 31) at those keys. Conclusion: every ciphertext in the \
    support of hybrid encryption of m under pk decrypts under sk to m. Applied to every key \
    pair in the support of key generation, this is the correctness requirement of \
    Definition 11.1 (p. 436) for the hybrid scheme; the hypotheses are needed only at the given \
    key pair and its encapsulated keys. Messages may have any type. Part (b), semantic \
    security, is not part of this entry: KEMINDCPA.hybrid_indcpaOn, in the same module, \
    assumes a KEM notion whose distinguisher also receives pk, which the exercise's KEM game \
    (p. 460) does not give it, and is registered as kem-dem-hybrid-ind-cpa-corrected."

register_result "kem-dem-hybrid-ind-cpa-corrected" where
  title := "KEM–DEM hybrid encryption is semantically secure when the KEM is secure against \
    distinguishers that also see the public key (corrected Exercise 11.9(b))"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Exercise 11.9(b), corrected: the KEM adversary also receives pk",
      locator := "Section 11.8, pp. 460–461" }
  ]
  theorems := [
    Cslib.Crypto.Encryption.KEMINDCPA.hybrid_indcpaOn,
    Cslib.Crypto.Encryption.KEMINDCPA.hybrid_indcpa
  ]
  scope := "A corrected form of Exercise 11.9(b). The exercise's KEM challenger sends only \
    (k_b, c_kem) (p. 460), and under that notion part (b) is false: if key generation outputs a \
    uniform pk with sk = pk and encapsulation returns (pk, []), both printed experiments show a \
    uniform key and an empty encapsulation, yet the hybrid with the one-time pad encrypts m as \
    pk ⊕ m, which anyone holding pk decrypts. The KEM hypothesis here, KEMINDCPA keyLen keyGen \
    encaps, also gives the distinguisher pk. It is the KEM security of Cramer and Shoup \
    (CramerShoup2003, Section 7.1.2, pp. 38–39 of the authors' revised manuscript of \
    August 14, 2003), restricted to adversaries that make no decryption queries, against uniform \
    strict PPT distinguishers, with the ideal key uniform on keyLen n-bit words and the \
    two-experiment advantage. The other hypotheses: DEMOneTimeKeyINDCPAOn valid encMsg keyLen \
    encryptSym, semantic security of the DEM (Attack Game 2.1 and Definition 2.2, p. 16) under a \
    uniform keyLen n-bit key against uniform strict PPT adversaries, for challenge pairs \
    admitted by valid; valid is polynomial-time computable and ignores the public key; key \
    generation, encapsulation and DEM encryption are uniform strict PPT. Conclusion: INDCPAOn \
    valid encMsg, semantic security (Attack Game 11.1 and Definition 11.2, pp. 436–437) of \
    hybridEncrypt encaps encryptSym, the hybrid scheme of the exercise (p. 461), against uniform \
    strict PPT two-stage adversaries, for the same valid. Taking valid to admit pairs of \
    messages of M of equal length, which is polynomial time because M is efficiently \
    recognizable (Definition 2.10, p. 31), gives the source's games; a wider valid is a stronger \
    assumption on the DEM. KEMINDCPA.hybrid_indcpa is the case in which every challenge pair is \
    admissible, the source's games when all messages of the type have one length. The \
    reductions hybridToKEMDistinguisher and hybridToDEMAdversary are certified strict PPT \
    (isPPT_hybridToKEMDistinguisher, isPPT_hybridToDEMAdversary). Asymptotic; \
    advantage_hybridGame_le_two_mul, in the same module, is the corrected exercise's bound \
    SSadv[A, E] ≤ 2 · SSadv[B_kem, E_kem] + SSadv[B_s, E_s], with the single hidden-bit \
    distinguisher hybridToKEMHiddenBitDistinguisher."

register_result "rsa-unit-preimage-variant" where
  title := "The RSA assumption implies its variant with a uniform unit preimage"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 10.5", locator := "Section 10.6.2, p. 416" }
  ]
  theorems := [
    Cslib.Crypto.RSAOneWay.rsaUnitOneWay
  ]
  scope := "Hypothesis: RSAOneWay gen, the RSA assumption (Attack Game 10.3 and Definition 10.5, \
    pp. 404–405) for a key law gen on RSADesc, with the preimage x uniform in Z_N and uniform \
    strict PPT inverters that read (1^n, N, e, y) and return a residue modulo N. Conclusion: \
    RSAUnitOneWay gen, the variant of p. 416 in which the challenger draws x uniformly from \
    Z_N^* and everything else is unchanged. The source fixes ℓ > 2 and an odd e > 2 and draws \
    keys with RSAGen(ℓ, e); here gen is any law on valid RSA parameters (distinct primes p and \
    q, and e·d ≡ 1 modulo (p − 1)(q − 1)), which need not be efficiently samplable, with no \
    condition on ℓ or e. The book's B is unitRSAToRSA, certified strict PPT \
    (isPPT_unitRSAToRSA): it passes a unit challenge to A, answers 0 with 0, and otherwise \
    factors N with gcd(y, N) and returns y^d′ for a recomputed decryption exponent d′. \
    Asymptotic; succProbability_rsaUnitInversionGame_le, in the same module, is the theorem's \
    bound uRSAadv[A, ℓ, e] ≤ RSAadv[B, ℓ, e] at every security parameter."

register_result "rsa-unit-preimage-converse" where
  title := "The unit-preimage RSA variant implies the RSA assumption when the primes are large"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercises 10.25–10.26",
      locator := "Section 10.11, p. 431" }
  ]
  theorems := [
    Cslib.Crypto.dist_uniformOfFintype_zmod_units_lt,
    Cslib.Crypto.RSAUnitOneWay.rsaOneWay,
    Cslib.Crypto.rsaOneWay_iff_rsaUnitOneWay
  ]
  scope := "Exercise 10.25 (dist_uniformOfFintype_zmod_units_lt): for distinct primes p and q of \
    at least ℓ bits, the uniform law on Z_pq and the uniform law on Z_pq^*, as residues, are at \
    statistical distance less than 4/2^ℓ = 2^-(ℓ-2); the source's primes, from RSAGen(ℓ, e), \
    have exactly ℓ bits. Exercise 10.26 (RSAUnitOneWay.rsaOneWay): RSAUnitOneWay gen, the \
    variant after Theorem 10.5 (p. 416), implies RSAOneWay gen (Attack Game 10.3 and \
    Definition 10.5, pp. 404–405), for a key law gen on valid RSA parameters, which need not be \
    efficiently samplable, whose primes have at least n bits at security parameter n for all \
    large n: the source's ℓ is n. Both games admit the same uniform strict PPT inverters, \
    reading (1^n, N, e, y) and returning a residue modulo N, so the source's B is A itself and \
    no reduction is defined. rsaOneWay_iff_rsaUnitOneWay adds the direction of Theorem 10.5 \
    (entry rsa-unit-preimage-variant) under the same condition on gen. \
    succProbability_rsaInversionGame_le_of_size, in the same module, is the exercise's bound \
    RSAadv[A, ℓ, e] ≤ uRSAadv[A, ℓ, e] + 4/2^ℓ when every key's primes have at least ℓ bits, \
    and RSAUnitOneWay.rsaOneWay_of_nonUnitFrac_le is the converse whenever the fraction of \
    non-units modulo N is bounded by a negligible function, which covers other prime lengths."

register_result "winternitz-domination-free" where
  title := "The Winternitz checksum encoding is domination free"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Lemma 14.5", locator := "Section 14.3.1, p. 593" }
  ]
  theorems := [
    Cslib.Crypto.OneTimeSignature.winternitzDigits_dominationFree
  ]
  scope := "DominationFree is Definition 14.4 (p. 591): for distinct messages m and m′, P(m) is \
    not coordinatewise at most P(m′). winternitzDigits d n0 n1 is the function P of \
    Section 14.3.1 (pp. 592–593): the n0 base-(d + 1) digits of the message, then the n1 \
    base-(d + 1) digits of the checksum d·n0 − (s_1 + … + s_n0). The theorem is stated for any \
    message type with an injection f into the integers below (d + 1)^n0 and any n1 with \
    d·n0 < (d + 1)^n1. The source's case is {0,1}^v read as the integers below 2^v, with n0 \
    least such that 2^v ≤ (d + 1)^n0 and n1 = ⌈log_(d+1)(d·n0)⌉ + 1, which satisfies the \
    inequality. Digits within each block are least significant first, where the source writes \
    numbers in the usual order; one fixed permutation of the coordinates of every P(m) does \
    not affect domination freeness. Unconditional combinatorics, with no adversary or \
    sampling. The Winternitz signature scheme and Theorem 14.4 are not formalized. In the same \
    module, winternitzDigitList_polyTime computes the encoding in polynomial time, and \
    winternitzDigits_one_eq_one_iff_mem_optSet relates the case d = 1 to P_opt (p. 593)."

register_result "optimized-lamport-containment-free" where
  title := "The checksum encoding P_opt of optimized Lamport signatures is containment free"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Lemma 14.3", locator := "Section 14.2.1, p. 588" }
  ]
  theorems := [
    Cslib.Crypto.OneTimeSignature.optSet_containmentFree
  ]
  scope := "ContainmentFree is Definition 14.3 (p. 587): for distinct messages m and m′, P(m) is \
    not a subset of P(m′). optSet v w is P_opt of Section 14.2.1 (p. 588) on v-bit messages: \
    the positions of the 1 bits of m, followed by a w-bit encoding of the number of 0 bits of \
    m. The theorem holds whenever v < 2^w; the source takes v a power of two and \
    w = log₂ v + 1. The checksum bits are least significant first, where Figure 14.2 \
    (p. 589) prints them most significant first; one fixed permutation of positions does not \
    affect containment freeness. Unconditional combinatorics, with no adversary or sampling. \
    The general Lamport signature scheme and Theorem 14.2 are not formalized here. \
    optWord_polyTime, in the same module, computes the encoding in polynomial time."

register_result "indexed-signature-counter-nonce" where
  title := "A secure indexed signature with a counter as its nonce is a secure stateful signature"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Section 14.6.4 nonce-based signatures, counter nonce",
      locator := "Section 14.6.4, pp. 602–603" }
  ]
  theorems := [
    Cslib.Crypto.IndexedSignatureScheme.IndexedEUFCMA.counterEUFCMA
  ]
  scope := "Premise: IndexedEUFCMA S, Definition 14.6 (p. 597): a q-indexed signature on the \
    message space {1, …, q} × M, secure against efficient adversaries whose signing queries \
    use distinct indices and who win with a valid signature on a new pair (u, m). Here \
    q = capacity n, computed in polynomial time from 1^n; indices run over 0, …, q − 1, in \
    unary; M is every bit string, which is security on every message space of polynomially \
    bounded word length at once. Signing may be randomized, where Definition 14.6 \
    requires deterministic signing: the theorem covers more schemes and is the source's for \
    deterministic ones. A request with a repeated index or an index u ≥ q is answered with \
    the empty word and not recorded, instead of being excluded from the adversary class; a \
    forger can predict these refusals, so the notions agree. A forgery counts only at an \
    index u < q. Conclusion: CounterEUFCMA S, the nonce-based use of Section 14.6.4 with the \
    nonce a counter (p. 603): the signing oracle signs its j-th request at index j and \
    answers the word (j, σ), refuses every request once j = q, and a forger wins with a valid \
    signature on a message it never had signed, at an index below q read from the signature \
    word. This is existential unforgeability for a nonce never used twice, as Section 14.6.4 \
    states it (p. 602). Same message space, refusals and index range as the premise. Forgers \
    in both games are uniform strict oracle-PPT machines. The proof's reduction \
    counterForger answers the j-th request by one indexed query at index j and forwards the \
    forgery with its index; it is certified oracle PPT (isOraclePPT_counterForger) and has \
    loss 1 (succProbability_counterEufCmaGame_le, in the same module). Asymptotic."

register_result "span-program-change-of-basis-equivalence" where
  title := "Right multiplication by an invertible matrix with top row e₁ gives an equivalent \
    monotone span program"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Lemma 22.15", locator := "Section 22.5.2.3, p. 982" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.SecretSharing.shareDist_linearUniformAccessScheme_mulRight
  ]
  scope := "Let P be a monotone span program (Definition 22.21, p. 978) whose matrices M_i have \
    size d_i × d over a finite field F, and R an invertible d × d matrix whose top row is e₁. \
    Then P.mulRight R, with matrices M_i R, is equivalent to P (Definition 22.23, p. 981): for \
    every secret, the linear secret sharing schemes that Construction 22.2 (p. 979) derives \
    from the two programs, with ρ_2, …, ρ_d uniform, give the same distribution of shares. The \
    source's field is Z_q for a prime q and its parties are 1, …, N; here F is any finite \
    field and the parties are any type. Unconditional, with no adversary. Theorems 22.13 and \
    22.14 are not part of this entry."

register_result "product-relation-dealer-soundness" where
  title := "Honest parties catch a dealer whose product relations fail, except with probability \
    2m/(q − m − 1)"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Lemma 23.1", locator := "Section 23.2.4.6, p. 1016" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.MPC.ProductRelation.eval_honestPartiesRun_accept_le
  ]
  scope := "Protocol 23.5 (Section 23.2.4.5, pp. 1014–1015) over Z_q for a prime q, with m \
    product relations (23.7). The dealer is corrupt: its messages to P₁ and P₂ (a_ki and b_ki \
    for k = 0, …, m, and c_ki for k = 0, …, 2m) are arbitrary values. The statement holds for \
    every such pair of messages, so it covers a randomized dealer, whose messages precede the \
    challenge. P₁ and P₂ are honest: each interpolates its polynomials (Lagrange.interpolate, \
    noncomputable, with no running-time claim), P₁ draws r uniformly from the elements of Z_q \
    other than 0, …, m, P₂ checks r, and both check (α₁ + α₂)(β₁ + β₂) = γ₁ + γ₂. Hypotheses: \
    (23.7) fails for the dealt values with k = 1, …, m; and 2m < q, which the source leaves \
    implicit, so that the interpolation nodes 0, …, 2m are distinct and the challenge set is \
    not empty. Conclusion: P₁ or P₂ finishes without aborting with probability at most \
    2m/(q − m − 1). Information-theoretic. eval_honestProtocol_eq_pure, in the same module, \
    is completeness: an honest dealer on values satisfying (23.7) makes both parties accept \
    with probability 1."

register_result "product-relation-simulation-privacy" where
  title := "In Protocol 23.5 a corrupt party's view is simulated from its own values alone"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Fact 23.2", locator := "Section 23.2.4.7, p. 1017" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.MPC.ProductRelation.eval_experiment0P1_eq_experiment1P1,
    Cslib.Crypto.Protocols.MPC.ProductRelation.eval_experiment0P2_eq_experiment1P2
  ]
  scope := "Experiments 0 and 1 of Section 23.2.4.7 (p. 1017) for Protocol 23.5 (p. 1015) over \
    Z_q for a prime q, with an honest dealer. eval_experiment0P1_eq_experiment1P1 (corrupt \
    P₁): the adversary chooses values (23.5) and (23.6) satisfying (23.7) on every outcome of \
    its sampler, receives P₁'s deal, chooses r and plays P₁ against the honest dealer and P₂ \
    (experiment0P1), or against the simulator S_D^(1) (simDeal and sim1Eval), which is given \
    only (23.5) (experiment1P1); the two output laws are equal. \
    eval_experiment0P2_eq_experiment1P2 is the same for a corrupt P₂ and the simulator \
    S_D^(2), which chooses r itself. Adversaries are arbitrary probabilistic programs with no \
    resource bound, as the source allows. In every experiment the corrupt party chooses its \
    Step 5 opening after receiving the honest party's, which admits more adversaries than the \
    simultaneous exchange of Step 5. Hypothesis 2m < q, which the source leaves implicit. The \
    dealer, the parties and the simulators sample uniformly from finite sets, as in the \
    source, and interpolate with Lagrange.interpolate (noncomputable); no running time is \
    claimed for the simulators (#5829)."

register_result "clique-eth-lower-bound" where
  title := "No f(k) n^o(k) or FPT algorithm for Clique under ETH"
  topic := "fine-grained complexity"
  sources := [
    { paper := CyganEtAl2015, theorem := "Theorem 14.21", locator := "p.485" }
  ]
  theorems := [
    Cslib.Complexity.ETH.not_clique_subexpVertex,
    Cslib.Complexity.ETH.not_clique_subexpEnc,
    Cslib.Complexity.ETH.clique_not_mem_FPT,
    Cslib.Complexity.DecidableInSubexpTime.threeSAT_of_clique_subexpVertex
  ]
  scope := "Clause-grouping reduction SAT.groupClique on Clique encCliqueInstance and \
    ThreeSAT (encCNF). Under ETH (relative to the library's native DecidableInTimeO model), no \
    decider for Clique runs in time f(k) · (|V| + 1)^o(k) · poly(|enc|) or f(k) · (|enc| + 1)^o(k) \
    with arbitrary f and real exponent g(k) satisfying g(k) ≤ ε k for large k; in particular \
    Clique ∉ FPT. Unconditional subexponential-time transfers to ThreeSAT hold without ETH. \
    This adapts the source's 3-Coloring vertex grouping to 3-CNF clauses and arbitrary f."

register_result "csp-bounded-treewidth" where
  title := "Exact counting and decision for finite-domain CSPs over bounded treewidth"
  topic := "parameterized algorithms"
  sources := [
    { paper := CyganEtAl2015, theorem := "Lemma 7.4 (nice trees)", locator := "p.161" }
  ]
  theorems := [
    Cslib.Algorithms.Lean.TreeDecomposition.ret_cspCountRootedM,
    Cslib.Algorithms.Lean.TreeDecomposition.ret_cspDecideRootedM,
    Cslib.Algorithms.Lean.TreeDecomposition.time_cspCountRootedM_le,
    Cslib.Algorithms.Lean.TreeDecomposition.ret_cspCountActiveRootedM,
    Cslib.Algorithms.Lean.TreeDecomposition.ret_cspCountNiceM_equiv
  ]
  scope := "Finite constraint domains Fin q (and arbitrary Fintype/Inhabited D via Equiv D \
    (Fin q)) over a supplied RootedTreeDecomposition of the primal or active primal graph. \
    Normalizes via toNiceTreePruned to at most (3 w + 5)(|V| + 1) nice nodes (size, not runtime \
    bound) and charges unit-cost TimeM inner-loop ticks bounded by (3 w + 5)(|V| + 1) · q^(w + 1) \
    · dpNodeCost w F (excluding recursive list-manipulation overhead like bagList, sem \
    evaluations, and unbounded integer arithmetic). The generic CSP-counting DP extension is an \
    adaptation/original implementation. Computing the tree decomposition is external."

register_result "kleene-post-incomparable" where
  title := "Kleene–Post theorem: existence of Turing-incomparable degrees"
  topic := "computability"
  sources := [
    { paper := KleenePost1954, theorem := unverified, locator := unverified },
    { paper := Soare1987, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Nat.RecursiveIn.kleene_post,
    TuringDegree.exists_incomparable,
    Nat.RecursiveIn.KleenePost.not_limA_le_limB,
    Nat.RecursiveIn.KleenePost.not_limB_le_limA
  ]
  scope := "Finite-extension construction of two sets A = {n | limA n = true} and \
    B = {n | limB n = true} whose characteristic functions A.indicator 1 and B.indicator 1 \
    are Turing incomparable (¬A ≤ᵀ B and ¬B ≤ᵀ A) under Mathlib's TuringReducible over \
    Nat.RecursiveIn.Code. The upper bound A, B ≤ᵀ ∅′ is proved in KleenePostJump; \
    incomparable computably enumerable degrees (Friedberg–Muchnik) remain open (#3379)."

register_result "kleene-post-below-jump" where
  title := "Kleene–Post theorem: incomparable sets constructed by finite extension lie below ∅′"
  topic := "computability"
  sources := [
    { paper := KleenePost1954, theorem := unverified, locator := unverified },
    { paper := Soare1987, theorem := unverified, locator := unverified },
    { paper := Simpson2005, theorem := "Theorem 2.6.4",
      locator := "§2.6, pp. 30–31 (November 1, 2005 draft)" }
  ]
  theorems := [
    kleene_post_below_jump,
    Nat.RecursiveIn.KleenePost.halts_reducibleTo_halting,
    Nat.RecursiveIn.KleenePost.rec_stageNat
  ]
  scope := "Proves that the Kleene–Post limit sequences limA and limB from KleenePost are \
    Turing reducible to the characteristic function halting.indicator 1 of the diagonal \
    ordinary-code halting set halting = {c | (Nat.Partrec.Code.eval (ofNat Code c) c).Dom}, \
    via primitive-recursive stage-bounded oracle evaluation (RecursiveInEvalnPrimrec) and \
    many-one reduction of the one-step extension question Halts to halting. Constructs total \
    Δ⁰₂ sets below ∅′; no c.e. property is proved. Friedberg–Muchnik, Sacks splitting/density \
    and Spector's minimal degree remain open (#3379)."

register_result "w-hierarchy-subset-xp" where
  title := "WeightedCircuitSAT, W[P] and every level W[t] of the W-hierarchy lie in XP"
  topic := "parameterized complexity"
  sources := [
    { paper := CyganEtAl2015, theorem := "weighted-circuit enumeration; Definition 13.16 (W[t])",
      locator := "Section 13.3, pp. 436–437 (authors' May 30, 2016 PDF)" }
  ]
  theorems := [
    Cslib.Complexity.WeightedCircuitSAT_mem_XP,
    Cslib.Complexity.WP_subset_XP,
    Cslib.Complexity.W_subset_XP,
    Cslib.Complexity.WCS_mem_XP,
    Cslib.Complexity.W_subset_WP,
    Cslib.Complexity.WP_eq_FPT_iff,
    Cslib.Complexity.IndependentSet_mem_XP,
    Cslib.Complexity.Clique_mem_XP
  ]
  scope := "Instances of WeightedCircuitSAT encode a one-output unbounded fan-in Boolean circuit \
    with unary input count, framed before the binary target weight k. Exhaustive search \
    over min(n, k)-tuples of input wires gives independent native multi-tape time and workspace \
    bounds C * 2^(D*k) * (L+1)^(D*k+D), hence XP membership. Library fpt-reduction closure gives \
    FPT ⊆ W[t] ⊆ WP ⊆ XP for every t and XP membership for WCS t d, Clique and IndependentSet. \
    WP denotes this library's reduction closure with arbitrary, potentially ineffective time \
    and parameter bounds; equivalence with the effective literature W[P] is not claimed. Circuits \
    are straight-line programs, with the basis conventions documented in WHierarchy.lean."

register_result "dnnf-size-multipartition-cover" where
  title := "DNNF size bounds the multi-partition rectangle cover number"
  topic := "circuit complexity"
  sources := [
    { paper := BovaCapelliMengelSlivovsky2016, theorem := unverified, locator := unverified },
    { paper := ArenasBroadrickLiewVanDenBroeck2026, theorem := "Theorem 3.1",
      locator := "§3.2, p. 9" }
  ]
  theorems := [
    Cslib.Circuits.NNF.exists_isCover,
    Cslib.Circuits.NNF.coverNumberFun_le_size,
    Cslib.Circuits.NNF.coverNumberFun_false_le_size
  ]
  scope := "NNF DAGs with literal and constant leaves and fan-in-two gates on finitely many \
    nodes, size = number of nodes; for at least two variables, a DNNF with s nodes computing f \
    gives a cover of f⁻¹(1) by s rectangles, each for its own partition with both sides of at \
    least n/3 variables."

register_result "ddnnf-negation-separation" where
  title := "d-DNNF is not polynomially closed under negation, given cubic edge expanders"
  topic := "circuit complexity"
  sources := [
    { paper := ArenasBroadrickLiewVanDenBroeck2026, theorem := "Theorem 1.1",
      locator := "§1, p. 3; proof in §5 (Proposition 5.1, Theorem 5.3)" }
  ]
  theorems := [
    Cslib.CubicEdgeColoring.ddnnf_negation_separation,
    Cslib.Circuits.NNF.exponential_separation_of_expanders
  ]
  scope := "For every cubic graph with a proper 3-edge-colouring on n ≥ 2 vertices that is a \
    balanced-cut γ-edge expander, f_G has a d-DNNF with at most 150n + 50 nodes and every DNNF \
    for ¬f_G has at least (48/47)^(γn/126) nodes. Theorem 1.1 itself (a 2^(cn) lower bound \
    with c > 0) is derived from a family of such expanders with γ > 0 on unboundedly many \
    vertex counts, which is Proposition 5.2 of the paper \
    and is a hypothesis, not proved (#4668)."

register_result "three-sat-complement-ph-collapse" where
  title := "3SAT reducing to its complement collapses PH to NP"
  topic := "complexity classes"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 5, Exercise 3",
      locator := "2007 public draft, printed p. 100 / PDF p. 116" }
  ]
  theorems := [Cslib.Complexity.PH_eq_NP_of_ThreeSAT_reducible_compl]
  scope := "Native polynomial-time many-one reduction with encCNF. ThreeSAT has clause width \
    at most three; its complement is inside all CNF Nat, including wider formulas. \
    The conclusion PH enc = NP enc holds for every explicit encoding enc."

register_result "arora-barak-relativized-ph-collapse" where
  title := "Relative P = NP collapses the polynomial hierarchy for the same oracle"
  topic := "complexity classes"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 5, Exercise §9",
      locator := "2007-01-08 public draft, printed p. 100 / PDF p. 116" }
  ]
  theorems := [Cslib.Complexity.PHWithOracle_subset_PWithOracle_of_eq_NPWithOracle]
  scope := "For an arbitrary fixed Boolean-word oracle O, equality of relative P and NP on \
    Boolean words implies the exercise's inclusion PH^O ⊆ P^O. The Lean conclusion holds on \
    every explicit instance encoding. A native polynomial-time multitape verifier queries O \
    after finitely many alternating blocks with polynomial lengths."

register_result "tautology-conp-complete" where
  title := "TAUTOLOGY is coNP-complete"
  topic := "NP-completeness"
  sources := [
    { paper := AroraBarak07, theorem := "Example 2.23",
      locator := "2007 public draft, Section 2.6, printed p. 57 / PDF p. 73" }
  ]
  theorems := [Cslib.Complexity.TAUTOLOGY_coNPComplete]
  scope := "Boolean formulas are the quantifier-free formulas of QBF Nat (variables, constants, \
    negation, conjunction, disjunction) in the prefix token encoding encQBF; TAUTOLOGY is a \
    total language on QBF Nat, so formulas with quantifiers are non-members. Membership in coNP \
    uses a native polynomial-time verifier; hardness is under total native polynomial-time \
    many-one reductions, through UNSAT by negation."

register_result "np-eq-conp-iff-threesat-tautology" where
  title := "NP = coNP iff 3SAT and TAUTOLOGY reduce to each other"
  topic := "complexity classes"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 2, Exercise 7",
      locator := "2007 public draft, printed p. 62 / PDF p. 78" }
  ]
  theorems := [Cslib.Complexity.NP_eq_coNP_iff_ThreeSAT_reducible_TAUTOLOGY]
  scope := "NP = coNP is quantified over every explicit instance encoding. The reductions are \
    native polynomial-time many-one reductions between ThreeSAT under encCNF (clause width at \
    most three) and TAUTOLOGY under encQBF (quantifier-free QBF Nat). The proof instantiates \
    NPComplete.NP_eq_coNP_iff_reducible, which holds for any NP-complete and coNP-complete \
    pair."

register_result "arora-barak-exact-indset-dp" where
  title := "EXACT INDSET is in DP"
  topic := "complexity classes"
  sources := [
    { paper := AroraBarak07, theorem := "Exercise 5 §8(a)",
      locator := "January 2007 draft, PDF p. 116; p. 5.10 (printed 100)" }
  ]
  theorems := [Cslib.Complexity.ExactIndependentSet_mem_DP]
  scope := "EXACT INDSET = instances ⟨G, k⟩ (library Graph with declared vertices, framed \
    graph and binary k) whose independence number is exactly k; DP = intersections of an NP \
    and a coNP language. DP-hardness (part (b)) is not included. Outside-fleet six-point \
    source check: review 5953416411 on PR #6402."

register_result "arora-barak-exact-indset-dp-hard" where
  title := "EXACT INDSET is DP-hard and therefore DP-complete"
  topic := "complexity classes"
  sources := [
    { paper := AroraBarak07, theorem := "Exercise 5 §8(b)",
      locator := "January 8, 2007 draft, printed p. 100 / PDF p. 116" }
  ]
  theorems := [Cslib.Complexity.ExactIndependentSet_dpHard,
    Cslib.Complexity.ExactIndependentSet_dpComplete]
  scope := "Every DP language under an explicit encoding reduces by a deterministic \
    polynomial-time many-one map to exact independence number on declared graph vertices, \
    using a framed graph and binary target. The reduction passes through SAT–UNSAT. \
    Completeness combines the hardness proof with the membership theorem from §8(a). \
    Outside-fleet source check: review 5958802809 on PR #6462."

register_result "goldreich-fixed-proof-system-np-conp" where
  title := "A fixed refutation system for unsatisfiable CNF formulas is polynomially bounded iff \
    NP = coNP"
  topic := "proof complexity"
  sources := [
    { paper := Goldreich2007DraftR6, theorem := "Theorem B.13 (with Definition B.12)",
      locator := "May 2007 draft r6.pdf, PDF p. 19; printed p. 527" }
  ]
  theorems := [
    Cslib.Complexity.ProofSystem.exists_polynomiallyBounded_iff_NP_eq_coNP
  ]
  scope := "CNF refutation form: proof systems for the unsatisfiable CNF formulas (encCNF) \
    instead of tautologies, which the draft discusses as refutations later in Appendix B.4. \
    Proof systems are Cook–Reckhow polynomial-time functions from proof words onto the set, not \
    Definition B.12 verifiers on a proof and a formula measured in their combined length. A \
    verifier becomes such a function by encoding both the formula and its certificate in the \
    proof word, and a function gives a verifier by evaluating it and comparing; polynomial \
    boundedness transfers between the two, but the proofs and their exact lengths need not \
    agree. PolynomiallyBounded bounds a shortest proof of each member by a polynomial in its \
    encoded length, the per-instance form of the bound on L_M(n). NP = coNP is stated for every \
    instance type and encoding. The Lean proof chooses M by cases on NP = coNP (the draft \
    invokes coNP-completeness): a polynomially bounded system if they are equal, otherwise the \
    exhaustive system ProofSystem.exhaustive. Outside-fleet six-point source check: review \
    5947873862 on PR #6300."

register_result "bounded-termination-exponential-completeness" where
  title := "Any-output bounded termination is in E but outside P and is EXP-complete"
  topic := "computational complexity"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Exercises 4.6–4.7",
      locator := "PDF p. 36, printed p. 152; bounded universal function: \
        PDF p. 28, printed p. 144" }
  ]
  theorems := [
    Cslib.Complexity.BoundedTermination.mem_E,
    Cslib.Complexity.BoundedTermination.notMem_P,
    Cslib.Complexity.BoundedTermination.polyTimeComplete_EXP,
    Cslib.Complexity.BoundedTermination.mk_desc_mem_iff,
    Cslib.Complexity.BoundedTermination.mem_reencode_iff
  ]
  scope := "Plain bit-word language with total description/input decoders and an MSB-first binary \
    clock; any halted output is allowed. E membership and EXP Karp-completeness hold on all \
    words; canonical native finite-machine triples have exact step-bound semantics. The chosen \
    representation is explicit: no arbitrary-encoding E invariance or sharp simulator bound \
    is claimed. Existing accepting-output-[true] BoundedHalting remains distinct."

register_result "valiant-zero-one-permanent-sharp-p-complete" where
  title := "Valiant: the 0/1 permanent and bipartite perfect-matching counting are #P-complete"
  topic := "counting complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 9.8",
      locator := "2007-01-08 draft, printed p. 175; PDF p. 191" },
    { paper := Goldreich2007Draft, theorem := "Theorem 6.20",
      locator := "February 2007 draft r3.pdf, PDF p. 23; printed p. 225" }
  ]
  theorems := [
    Cslib.Complexity.zeroOnePermanent_sharpPMetricComplete,
    Cslib.Complexity.zeroOnePermanent_computableInPolyTimeWithOracle,
    Cslib.Complexity.bipartitePerfectMatchingCount_sharpPMetricComplete,
    Cslib.Complexity.bipartitePerfectMatchingCount_computableInPolyTimeWithOracle,
    Cslib.Complexity.intPermanent_sharpPMetricHard
  ]
  scope := "Dense Boolean tables (encBoolTable) read as n x n 0/1 matrices, and the bipartite \
    graphs on Fin n + Fin n they describe (Mathlib perfect matchings). Membership in #P by a \
    native permutation-matrix verifier; hardness under one-query metric reductions composed \
    from #3SAT, Goldreich's Propositions 6.21 and 6.22. The books' Cook-reduction form (Arora \
    and Barak Definition 9.5, FP with a bit oracle) is derived as a native polynomial-time \
    oracle program reading the permanent's bits. Arora and Barak's XOR-gadget proof and its \
    constant 4^(3m) are not formalized; the proof uses Goldreich's gadget."

register_result "bilinear-finite-field-fingerprint" where
  title := "Two-vector matrix identity fingerprint"
  topic := "randomized verification"
  sources := [
    { paper := Goldreich2007DraftR5, theorem := "Exercise 9.22",
      locator := "r5.pdf; PDF page 70 / printed page 452; rendered guideline exponent checked" }
  ]
  theorems := [Cslib.Probability.toOuterMeasure_bilinear_ne_zero_ge,
    Cslib.Probability.toOuterMeasure_bilinear_zmod_ne_zero_ge,
    Cslib.Probability.toOuterMeasure_bilinear_vecMulVec]
  scope := "Arbitrary finite field and finite rectangular matrix with M ≠ 0. Independent \
    uniform product sampling detects a nonzero bilinear fingerprint with probability at \
    least (1 - 1/|F|)^2. Nonzero outer products attain equality, including characteristic \
    two. No runtime bound or general rank formula."

register_result "random-walk-edge-hitting-time" where
  title := "The random walk crosses an edge of a connected graph in expected time at most 2|E|"
  topic := "randomized complexity"
  sources := [
    { paper := Goldreich2007Draft, theorem := "Exercise 6.19 (completing Proposition 6.13)",
      locator := "February 2007 draft r3.pdf, PDF p. 56; printed p. 258" }
  ]
  theorems := [
    Cslib.Probability.MarkovChain.hittingTime_randomWalk_le_of_adj,
    Cslib.Probability.MarkovChain.hittingTime_randomWalk_add_degree_le,
    Cslib.Probability.MarkovChain.degree_mul_returnTime_randomWalk,
    Cslib.Probability.MarkovChain.hittingTime_randomWalk_le_dist_mul
  ]
  scope := "Finite simple graphs (Mathlib SimpleGraph) with the simple random walk as a \
    MarkovChain; connectedness assumed. Expected hitting and return times are exact \
    extended-real tail sums of the probabilities of avoiding the target, not finite-horizon \
    approximations. Proves E_u[tau_v] + deg v <= 2|E| for every edge {u,v}, Kac's formula \
    deg v * E_v[tau+_v] = 2|E|, and E_u[tau_v] <= 2|E| dist(u,v). Proposition 6.13's cover-time \
    bound and the log-space USTCON algorithm are not included."

register_result "goldreich-modular-square-root-descent" where
  title := "Square roots modulo a prime from a quadratic non-residue"
  topic := "randomized algorithms"
  sources := [
    { paper := Goldreich2007Draft, theorem := "Exercise 6.16, items 1-3",
      locator := "February 2007 draft r3.pdf, PDF p. 55; printed p. 257, with footnote 23" }
  ]
  theorems := [
    Cslib.Complexity.ModularSquareRoot.pow_add_one_div_four_sq_modEq,
    Cslib.Complexity.ModularSquareRoot.sq_eq_of_pow_mul_pow_eq_one,
    Cslib.Complexity.ModularSquareRoot.descentExponents_spec,
    Cslib.Complexity.ModularSquareRoot.computableInPolyTime_descentExponents,
    Cslib.Complexity.ModularSquareRoot.sqrtMod_sq,
    Cslib.Complexity.ModularSquareRoot.computableInPolyTime_sqrtMod
  ]
  scope := "Deterministic items only. Inputs are a prime P, a quadratic residue s modulo P and, \
    for P ≡ 1 (mod 4), a supplied quadratic non-residue t (t ^ (P / 2) = -1 in ZMod P); \
    primality, squareness and the non-residue condition are input promises. The descent \
    (footnote 23) computes an odd e and an even e' with s ^ e * t ^ e' = 1 for non-zero s, \
    and sqrtMod returns a square root of s (zero included); both are native polynomial-time \
    on binary naturals. The randomized search for t (item 4) is not included."
register_result "regular-random-walk-hitting-times" where
  title := "Random walks on regular multigraphs: unique stationary law, return and hitting times"
  topic := "randomized complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 7, Exercise 9(b)(i), (c), (d)",
      locator := "2007-01-08 draft, printed p. 133; PDF p. 149" }
  ]
  theorems := [
    Cslib.RotationMap.isStationary_randomWalk_iff,
    Cslib.RotationMap.returnTime_randomWalk_eq_card,
    Cslib.RotationMap.returnTime_randomWalk_le_ten_mul_sq,
    Cslib.RotationMap.hittingTime_randomWalk_le_hundred_mul,
    Cslib.RotationMap.ten_mul_card_filter_walkAt_ne_le
  ]
  scope := "d-regular multigraphs presented by rotation maps (loops and parallel edges allowed), \
    random walk along a uniform edge label as a MarkovChain. Exact extended-real expectations. \
    (b)(i): on a connected graph the uniform PMF is the unique stationary law. (c): the expected \
    return time to u equals the size of u's component, hence n when connected and at most 10 n^2. \
    (d): with d <= n, E_{u,v} <= 100 k n^2 along a path of length k, and at most a tenth of the \
    label sequences of length 1000 n^3 avoid t. Part (b)(ii) (visit-count concentration) and \
    part (e) are not included."

register_result "regular-random-walk-visit-concentration" where
  title := "Visit counts of random walks on connected regular multigraphs concentrate around t/n"
  topic := "randomized complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 7, Exercise 9(b)(ii)",
      locator := "2007-01-08 draft, printed p. 133; PDF p. 149" }
  ]
  theorems := [
    Cslib.RotationMap.exists_visits_mem_Icc,
    Cslib.RotationMap.eventually_visits_mem_Icc,
    Cslib.RotationMap.exists_abs_sum_walk_pow_le
  ]
  scope := "Connected d-regular multigraphs presented by rotation maps; probability is the \
    fraction of the d^t label sequences. For every u, v and eps > 0, for all large t, the \
    number of visits to v at times 1..t lies in [(1-eps)t/n, (1+eps)t/n] with probability at \
    least 1 - eps. No aperiodicity is assumed; no explicit rate in t is given."

register_result "goldreich-expander-varying-density-hitting" where
  title := "Expander-walk varying-density product and constant-set bound"
  topic := "pseudorandomness"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 8.43, equation (8.24)",
      locator := "March 2007 draft, printed p. 381 / PDF p. 117" }
  ]
  theorems := [
    Cslib.RotationMap.dens_filter_forall_walkAt_mem_le_product,
    Cslib.RotationMap.dens_filter_forall_walkAt_mem_le_product_of_spectralExpansion_le,
    Cslib.RotationMap.dens_filter_forall_walkAt_mem_le_rpow_of_spectralExpansion_le
  ]
  scope := "Finite nonempty rotation map with nonempty incident slots; uniform initial vertex \
    and independent uniform slot choices. Length counts t+1 vertices. Individual densities \
    retained, with explicit transport to lambda/d and the constant-set real half-length power. \
    No machine uniformity, runtime or Exercise 8.44 concentration claim."

register_result "goldreich-small-bias-stretch-limits" where
  title := "Small-bias generators: stretch limits for low-degree and linear generators"
  topic := "pseudorandomness"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 8.37",
      locator := "March 2007 draft, printed pp. 379–380 / PDF pp. 115–116" }
  ]
  theorems := [
    Cslib.BitString.le_sum_choose_of_isSmallBias,
    Cslib.BitString.card_lt_card_of_isSmallBias,
    Cslib.BitString.not_exists_linearMap_of_isSmallBias
  ]
  scope := "Uniform seeds; IsSmallBias ε of the output distribution with ε < 1. If every output \
    bit of G : {0,1}^k → {0,1}^ℓ is a GF(2) polynomial of total degree at most d in the seed \
    bits, then ℓ ≤ ∑_{i=1}^d C(k,i). Corollaries: fewer output bits than seeds for any finite \
    seed space (so ℓ < 2^k), and no GF(2)-linear G with ℓ > k."

register_result "goldreich-read-once-prg-small-bias" where
  title := "Space-bounded pseudorandom generators are 2ε-bias generators"
  topic := "pseudorandomness"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 8.38 (corrected: 2ε-bias)",
      locator := "March 2007 draft, printed p. 380 / PDF p. 116" }
  ]
  theorems := [Cslib.Crypto.PRG.Generator.Secure.isSmallBias]
  scope := "A generator G : {0,1}^k → {0,1}^ℓ fooling the read-once programs of width 2^s, \
    s ≥ 1, with error ε is a 2ε-bias generator. The printed conclusion ε-bias is false: \
    exists_secure_not_isSmallBias gives σ ↦ σσ on one seed bit, which fools every test with \
    error 1/2 but has bias 1. Under the source's Eq. (8.18) bias is twice the parity \
    automaton's distinguishing gap."

register_result "goldreich-read-once-prg-stretch" where
  title := "Space-bounded pseudorandom generators with error below 1/2 have ℓ < 2^k"
  topic := "pseudorandomness"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 8.25(2) (corrected: ε < 1/2)",
      locator := "March 2007 draft, printed p. 376 / PDF p. 112" }
  ]
  theorems := [Cslib.Crypto.PRG.Generator.Secure.lt_two_pow]
  scope := "A generator G : {0,1}^k → {0,1}^ℓ fooling the read-once programs of width 2^s, \
    s ≥ 1, with error ε < 1/2 has ℓ < 2^k, via the 2ε-bias bound and Exercise 8.37. The \
    printed hypothesis ε < 1 does not suffice: σ ↦ σσ has ℓ = 2 = 2^1 with error 1/2 \
    (exists_secure_not_isSmallBias)."

register_result "goldreich-adaptive-t-wise-independence" where
  title := "Adaptive block tests of t-wise independent generators"
  topic := "pseudorandomness"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 8.29",
      locator := "March 2007 draft, printed pp. 376–377 / PDF pp. 112–113" }
  ]
  theorems := [Cslib.Probability.IsKWiseIndependentHash.bind_map_eval_eq]
  scope := "With a uniform seed and t-wise independent Boolean blocks, an adaptive test has \
    the same output law as on uniform bits. A test samples independent coins to select a \
    decision tree and reads bits from at most t distinct blocks on each input. This includes \
    whole-block tests. Outside-fleet source check: review 5954380213 on PR #6421."

register_result "goldreich-adaptive-query-separation" where
  title := "Adaptive t-query tests separate a law with almost uniform t-bit marginals"
  topic := "pseudorandomness"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 8.32(1)",
      locator := "March 2007 draft, printed pp. 377–378 / PDF pp. 113–114" }
  ]
  theorems := [Cslib.DecisionTree.exists_dist_map_restrict_le_and_map_eval_eq_printed_length]
  scope := "For each positive t, a law on exactly 2^(t−1) bits has total variation at most \
    t/2^t from uniform on every fixed t-coordinate marginal. A decision tree of depth at most \
    t accepts the law surely and uniform input with probability 1/2. The construction shares \
    data bits across address pairs to attain the printed length. The guideline uses t−1 \
    additional bits. Outside-fleet source check: \
    https://github.com/cslib-community/cslib-frontier/pull/6467#pullrequestreview-5958887313"

register_result "goldreich-adaptive-almost-t-wise-independence" where
  title := "Adaptive bit tests of almost t-wise independent distributions"
  topic := "pseudorandomness"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 8.32(2)",
      locator := "March 2007 draft, printed p. 378 / PDF p. 114" }
  ]
  theorems := [Cslib.DecisionTree.abs_bind_map_eval_apply_sub_le]
  scope := "For a law on n bits with n ≥ t, if every t-bit marginal has statistical distance \
    at most ε from uniform, an adaptive test reading at most t distinct positions on each \
    input has distinguishing gap at most 2^t ε. The test uses finitely many random-coin \
    outcomes. Outside-fleet source check: review 5954380213 on PR #6421."

register_result "arora-barak-nonexplicit-prg" where
  title := "Non-explicit pseudorandom generators: length and indistinguishability properties"
  topic := "pseudorandomness"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 16, Exercise 2 (corrected at seed length ≤ 1)",
      locator := "January 8, 2007 draft; printed 318 / PDF 334; Definition 16.2 printed 283 / \
        PDF 299; rounding convention printed 7 / PDF 23" }
  ]
  theorems := [Cslib.Complexity.exists_generator_advantage_lt,
    Cslib.Complexity.exists_isCircuitTest_le_advantage_one]
  scope := "Outside check: PR #6271, review 5947409116. epsilon = 1/10; one map G on words \
    and output length S(l) = ceil(2^(l/10)) for l >= 2 and S(l) = l for l <= 1, monotone, \
    with |G(z)| = S(|z|), and for every l advantage below 1/10 against every deterministic \
    De Morgan circuit with at most S(l)^3 non-input gates (uniform seed versus uniform \
    output). Only these length and indistinguishability properties are covered: \
    polynomial-time computability of S (a condition of Definition 16.2) is not proved, and \
    G has no time bound, as the exercise allows. The printed form fails at l = 1 for every \
    epsilon > 0 and every G under the draft's ceiling convention; the witness has at most \
    four gates, at most m + 5 <= m^3 nodes when inputs and an output node are counted."

register_result "finite-abelian-homomorphism-testing" where
  title := "Finite abelian homomorphism testing and plurality correction"
  topic := "property testing"
  sources := [
    { paper := Goldreich2007DraftR5, theorem := "Exercise 9.21(1)–(3)",
      locator := "r5.pdf; PDF 69–70 / printed 451–452; rendered notation checked" }
  ]
  theorems := [Cslib.HomomorphismTesting.concentration,
    Cslib.HomomorphismTesting.plurality_add, Cslib.HomomorphismTesting.closeness,
    Cslib.HomomorphismTesting.distance_attained, Cslib.HomomorphismTesting.min_le_rejection]
  scope := "Arbitrary finite additive commutative groups, including trivial groups. Uniform \
    independent rejection epsilon and attained minimum normalized homomorphism \
    disagreement delta. Every plurality has mass at least 1-2epsilon; below 1/6 it is \
    a homomorphism with disagreement at most 2epsilon. Unconditionally epsilon >= \
    min(1/6,delta/2). No efficiency or encoding claim."

register_result "linear-space-ne-np" where
  title := "Book: linear space is not NP"
  topic := "space complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 3, Exercise 2",
      locator := "2007 public draft, printed p. 73 / PDF p. 89" },
    { paper := Book1974, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.DSPACE_ne_NP,
    Cslib.Complexity.DSPACE_pow_ne_of_polyTimeReducible_mem
  ]
  scope := "DSPACE encBits (fun n => n) ≠ NP encBits on bit words. DSPACE counts visited work \
    cells of one native multi-tape machine; the draft's Definition 4.1 counts ever-non-blank \
    cells. More generally DSPACE (n ^ k), k ≥ 1, differs from every class closed under \
    polynomial-time many-one reductions, by polynomial space padding and the space hierarchy."

register_result "arora-barak-draft-leftover-hash" where
  title := "Draft leftover hash lemma with entropy k/delta"
  topic := "pseudorandomness"
  sources := [
    { paper := AroraBarak07, theorem := "Lemma 16.42; Chapter 16, Exercise 12",
      locator := "January 8, 2007 draft; printed 308 / PDF 324; exercise printed 319 / PDF 335" }
  ]
  theorems := [Cslib.Probability.IsUniversalHash.isStrongExtractor_of_entropy_div,
    Cslib.Probability.IsUniversalHash.isExtractor_append_of_entropy_div]
  scope := "All n,k,t and positive delta. Uniform independent seed, distinct-input collision \
    bound (1+delta)/2^k, source min-entropy at least k/delta, statistical distance at most \
    sqrt(2 delta). Concatenated output is digest followed by seed. Includes zero digest \
    and large delta; no efficiency or short-seed assertion."

register_result "goldreich-expander-visit-count" where
  title := "Expander-walk selected-time hitting and visit-count tails"
  topic := "pseudorandomness"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 8.44",
      locator := "March 2007 draft, printed p. 381 / PDF p. 117" }
  ]
  theorems := [
    Cslib.RotationMap.dens_filter_selected_walkAt_mem_le,
    Cslib.RotationMap.expect_choose_visitCount_le,
    Cslib.RotationMap.dens_filter_visitCount_ge_le,
    Cslib.RotationMap.dens_filter_visitCount_gt_le,
    Cslib.RotationMap.dens_filter_visitCount_gt_lt,
    Cslib.RotationMap.dens_filter_visitCount_half_lt
  ]
  scope := "Finite nonempty rotation map and ports; uniform initial vertex and independent \
    ports. Length L=t+1 counts vertices, including time zero. Arbitrary selected \
    times, factorial moments, integer tails and strict half-visits for every positive \
    L. The source strict integer bound requires 1<=m<=L and rho+eta^2>0; alpha*L needs \
    an integer convention. No sampler/runtime claim."

register_result "tally-np-exp-nexp" where
  title := "Easy tally NP collapses EXP and NEXP"
  topic := "complexity classes"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 2, Exercise 23",
      locator := "2007 public draft, printed p. 64 / PDF p. 80" },
    { paper := HartmanisImmermanSewelson1985, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.EXP_eq_NEXP_of_tally,
    Cslib.Complexity.E_eq_NE_of_tally,
    Cslib.Complexity.expPaddedNPEasy_of_tally
  ]
  scope := "(∀ L ∈ TALLY, L ∈ NP encBits → L ∈ P encBits) → EXP enc = NEXP enc and E enc = NE enc \
    for every encoding enc; TALLY is the set of bit-languages of all-true words. Only this \
    direction of Hartmanis–Immerman–Sewelson is proved."

register_result "uniform-probing-expected-probes" where
  title :=
    "Expected probe count for unsuccessful search and fresh-key insertion under uniform probing"
  topic := "algorithms"
  sources := [
    { paper := CLRS2009, theorem := "Theorem 11.6 and Corollary 11.7",
      locator := "Section 11.4, pp. 274–276" }
  ]
  theorems := [
    Cslib.DataStructure.Dictionary.UniformProbing.expect_unsuccessfulProbes_le,
    Cslib.DataStructure.Dictionary.UniformProbing.expect_unsuccessfulProbes_le_two,
    Cslib.DataStructure.Dictionary.UniformProbing.expect_probeCount_of_eq_none_le,
    Cslib.DataStructure.Dictionary.UniformProbing.expect_probeCount_of_eq_none_le_two
  ]
  scope := "Uniform full-cycle probing over m slots: expect_unsuccessfulProbes_le and \
    expect_unsuccessfulProbes_le_two sample a single uniform permutation σ : Equiv.Perm (Fin m) \
    via PMF.uniformOfFintype against any occupied slot set O : Finset (Fin m) with O.card < m \
    (or 0 < m and 2 * O.card ≤ m). expect_probeCount_of_eq_none_le and \
    expect_probeCount_of_eq_none_le_two sample independent per-key permutations \
    π : Fin U → Equiv.Perm (Fin m) via PMF.uniformOfFintype (lazy-sampling equivalence proved \
    separately in uniform_interpret_eq_lazy_perm) and run any non-adaptive admissible history \
    ops of the insert-only bounded-capacity dictionary specification Dictionary.spec U V n_max \
    (ValidHistory, empty, run, dom, with n_max ≤ m) on Table U m := Fin m → Option (Fin U × ℕ) \
    via runTable and TableRep. Probe counts unsuccessfulProbes O σ := 1 + missedProbes O σ and \
    probeCount T u (π u) := unsuccessfulProbes (otherOccupiedSlots T u) (π u) count all \
    inspected slots along the probe sequence up to and including the first slot outside O \
    (< m). Proves ℝ≥0∞ expected probe bounds ≤ m / (m - n) for any absent key s u = none with \
    (Dictionary.dom s).card = n < m, and ≤ 2 under 2 * n_max ≤ m. Abstract uniform-hashing table \
    model only: no concrete hash construction or Word-RAM runtime claim, and excludes the \
    uniform-key-averaged logarithmic endpoint of CLRS Theorem 11.8 (the module formalizes only a \
    per-key intermediate step)."

register_result "owp-iterate-one-way" where
  title := "Iterates of a one-way permutation are one-way, for rational exponents and \
    certified counts"
  topic := "cryptography"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 10, Exercise 3",
      locator := "Web draft 2007-01-08, printed p. 204; PDF p. 220" }
  ]
  theorems := [Cslib.Crypto.OneWayPermutation.iterate_ceil_rpow,
    Cslib.Crypto.OneWayPermutation.iterateByLength]
  scope := "Covers every rational exponent c = p / q (count ⌈|x| ^ c⌉) and every other exponent \
    whose rounded count has a polynomial-time unary certificate; no uniform algorithm is given \
    for an arbitrary real c. The general form allows any polynomial-time unary count that is \
    eventually nonzero. OneWayPermutation is a length-preserving bijection on List Bool, \
    polynomial-time computable, with negligible inversion probability for every uniform strict \
    PPT inverter given unary n and f x for uniform n-bit x (any preimage accepted). This is the \
    asymptotic reading of the draft's Definition 10.1, which bounds inversion time and success \
    concretely; the reduction is exact and adds up to k n - 1 evaluations of f, so concrete \
    bounds transfer with that overhead. Source check: outside-fleet review on PR #6274."

register_result "owf-iterate-not-one-way" where
  title := "Iterates of a one-way function need not be one-way"
  topic := "cryptography"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 10, Exercise 4",
      locator := "Web draft 2007-01-08, printed p. 204; PDF p. 220" }
  ]
  theorems := [Cslib.Crypto.exists_oneWay_not_oneWay_iterate_ceil_rpow,
    Cslib.Crypto.exists_oneWay_not_oneWay_iterate]
  scope := "OneWay on List Bool: polynomial-time computable, with negligible inversion \
    probability for every uniform strict-PPT inverter given unary n and f x for uniform n-bit \
    x (any preimage accepted). If some OneWay function exists, one OneWay f with a single \
    polynomial-time output length m(n) per input length (Definition 10.1's family) has \
    x ↦ f^[⌈|x| ^ c⌉] x not OneWay for every real c > 0, and more generally for every count \
    that is at least 2 for all large n. The draft's parametric Definition 10.1 is read \
    asymptotically; the draft's hint only asks for a counterexample, and the construction is \
    the library's own. Source check: independent review on PR #6278."

register_result "mpda-well-nested-reachability" where
  title := "Inductive saturation characterizes well-nested reachability"
  topic := "automata theory"
  sources := [
    { paper := AkshayGastinKrishnaRoychowdhury2020, theorem := "Lemma 1",
      locator := "arXiv:2002.05950v2, Section 3, paragraph \"Binary well-nested reachability \
        for MPDA\"; Algorithm 2 in Appendix B" }
  ]
  theorems := [Cslib.Automata.MPDA.wellNestedReach_iff]
  scope := "For every MPDA, with arbitrary control-state and input types, finitely many \
    stacks and no finiteness assumption, and all control states s and s': s' is related to s \
    by WellNestedReach exactly when some well-nested sequence of transitions labels a finite \
    run of the control from s to s'. WellNestedReach is the least relation containing the \
    identity pairs, closed under prefixing a nop transition, and closed under pushPop: a push \
    from s1 to s2, a related pair (s2, s3), the pop of the same stack and symbol from s3 to s4, \
    and an independently related suffix (s4, s5) give the pair (s1, s5); the suffix supplies \
    the concatenation needed for consecutive matched pairs. This is the relational \
    characterization of the table computed by Algorithm 2, which starts from the identity pairs \
    and the nop transitions; the finite iteration of Algorithm 2, its termination and the \
    equality of its output with WellNestedReach are not formalized. Source check: outside-fleet \
    agent review (review_6193_endpoint, codex-coord-20261111-1634) on PR #6474, against \
    arXiv:2002.05950v2 Section 2 p. 4, Section 3 pp. 7-8 and Appendix B p. 22."
register_result "offline-dictionary-attack" where
  title := "The offline dictionary attack recovers a password in the dictionary, or one with the \
    same hash, with at most |D| hash evaluations"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "offline dictionary attack (18.1) (unnumbered)",
      locator := "Section 18.3.1.2, pp. 721–722" }
  ]
  theorems := [
    Cslib.Crypto.exists_evalPure_dictionaryPreimageSearch_of_mem,
    Cslib.Crypto.isQueryBounded_dictionarySearch,
    Cslib.Crypto.dictionarySearch_inverts
  ]
  scope := "The hash H : X → Y is an oracle, and the dictionary D is a list of candidate \
    passwords searched in order; input : P → X derives the hashed input, the identity for \
    (18.1). exists_evalPure_dictionaryPreimageSearch_of_mem: on vk = H(pw) with pw ∈ D, the \
    search returns some w ∈ D with H(w) = H(pw), the book's 'pw, or possibly some pw′ with \
    H(pw) = H(pw′)'. isQueryBounded_dictionarySearch: at most |D| evaluations of H on every \
    path. The book states running time O(|D|), counting one evaluation of H as one time unit; \
    the bound here counts evaluations of H only, leaves comparisons uncounted and states no \
    running time in a machine model. dictionarySearch_inverts: for every H and every law μ of \
    the password, the search, with at most |D| evaluations on every challenge, inverts \
    pw ↦ H(pw) with probability at least μ(D); this probability form is the library's. The \
    preprocessing and batch attacks (18.2)–(18.3) and the salted search of Section 18.4.1, in \
    the same module, are not listed: the book's attack-phase times rest on table lookups that \
    the module does not count."

register_result "perfect-secrecy-zero-semantic-advantage" where
  title := "Perfectly secure ciphers, the one-time pad and the variable-length one-time pad have \
    semantic-security advantage zero against every adversary"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Example 2.9 and Exercise 2.7",
      locator := "Section 2.2.2, p. 17; Section 2.6, p. 39" }
  ]
  theorems := [
    Cslib.Crypto.Cipher.advantage_oneTimeExperiment_eq_zero_of_perfectlySecret,
    Cslib.Crypto.Cipher.advantage_oneTimeExperiment_eq_zero_of_ciphertextDist_eq,
    Cslib.Crypto.Cipher.advantage_oneTimeExperiment_otpCipher,
    Cslib.Crypto.Cipher.advantage_oneTimeExperiment_variableLengthOTPCipher
  ]
  scope := "Cipher.oneTimeExperiment is Attack Game 2.1 (p. 16) for one cipher: a key from the \
    key sampler and a challenge pair chosen by a two-stage adversary (TwoStage: randomized, \
    computationally unbounded, with any state type), checked by an admissibility predicate; an \
    inadmissible pair makes the experiment output 0. \
    advantage_oneTimeExperiment_eq_zero_of_perfectlySecret: if the cipher's key law and \
    encryption laws are those of a PerfectlySecret EncScheme, SSadv[A, E] = 0 for every \
    adversary and every predicate. The cipher may be randomized and the key law arbitrary, \
    where Example 2.9 takes a deterministic cipher, perfectly secure under Definition 2.1 with a \
    uniform key. advantage_oneTimeExperiment_eq_zero_of_ciphertextDist_eq: the same conclusion \
    when only admissible pairs have equal ciphertext laws. \
    advantage_oneTimeExperiment_otpCipher: the one-time pad on l-bit words (Example 2.1) with a \
    uniform key, for any predicate. advantage_oneTimeExperiment_variableLengthOTPCipher: the \
    variable-length one-time pad of Example 2.2, with L-bit keys and messages of at most L bits, \
    under the book's equal-length admissibility; this pad is not perfectly secure unless L = 0, \
    so this case does not follow from the first. Information-theoretic; no assumption."

register_result "message-recovery-from-semantic-security" where
  title := "A semantically secure cipher with message space {0,1}^L is secure against message \
    recovery"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 2.7, for message spaces {0,1}^L",
      locator := "Section 2.2.3.1, pp. 18–19 (Attack Game 2.2, p. 18; Definition 2.3 and \
        Theorem 2.7, p. 19)" }
  ]
  theorems := [
    Cslib.Crypto.Encryption.DEMOneTimeKeyINDCPAOn.negligible_messageRecoveryWordAdvantage
  ]
  scope := "Theorem 2.7 is stated for any message space M. Its proof's adversary B submits two \
    independent uniform messages of M, which Attack Game 2.1 (p. 16) admits only when they have \
    the same length, so the proof needs all messages of M to have one length. The statement \
    fails otherwise: for M = {0, 00} with bit length and the identity cipher, every admissible \
    pair has m₀ = m₁, so SSadv is 0, while MRadv is 1/2. This entry states the theorem for \
    M = {0,1}^L with L = msgLen n at security parameter n. The cipher is a family of randomized \
    encryption algorithms encryptSym n k m on bit words, with no system parameter. Its key is a \
    uniform keyLen n-bit word: the book's uniformly sampled key space K is the set of keyLen \
    n-bit words. The premise is semantic security (Attack Game 2.1 and Definition 2.2, p. 16) \
    against uniform strict PPT two-stage adversaries, for exactly the challenge pairs in M: \
    DEMOneTimeKeyINDCPAOn with the predicate that both messages have msgLen n bits. A pair \
    outside M makes both experiments output 0, and nothing is assumed about messages of other \
    lengths. Encryption need not be efficient or correct, since the proof uses neither, and \
    decryption is not modeled. Conclusion: every uniform strict PPT adversary A, given 1ⁿ and \
    c ← E(k, m) for a uniform m ∈ {0,1}^(msgLen n), has negligible \
    MRadv[A, E] = |Pr[m̂ = m] − 1/2^(msgLen n)| (messageRecoveryWordAdvantage; Attack Game 2.2, \
    p. 18, and Definition 2.3, p. 19). Lean adversaries output arbitrary words. The hypothesis \
    hA_len, that every output in the support of A n c has msgLen n bits, encodes the game's \
    m̂ ∈ M. Without it, at msgLen n = 1 an adversary that outputs the empty word never wins and \
    has MRadv = 1/2, as the module's tests check. The theorem also assumes msgLen is computable \
    in polynomial time in unary. This follows from the book's requirements: M is efficiently \
    recognizable (Definition 2.10, p. 31) and its words have polynomially bounded length \
    (Definition 2.9, p. 30), so L is found by testing 0^i ∈ M up to that bound. The reduction \
    messageRecoveryWordToDEMAdversary is the book's B: it draws uniform m₀ and m₁, forwards c \
    to A and outputs 1 iff m̂ = m₁. isPPT_messageRecoveryWordToDEMAdversary certifies it \
    uniform strict PPT, and messageRecoveryWordAdvantage_eq_demKeyGameOn, in the same module, \
    is the proof's equality MRadv[A, E] = SSadv[B, E] at each n; the book notes that equality \
    holds in (2.5). The parity-prediction tests check a cipher that meets this premise and \
    fails the equal-length notion DEMOneTimeKeyWordINDCPA. \
    messageRecoveryAdvantage_eq_advantage_messageRecoveryReduction, in the same module, is the \
    equality for one cipher over any finite M with any key sampler when every pair is \
    admissible, and is not listed."

register_result "parity-prediction-from-semantic-security" where
  title := "A semantically secure cipher with message space {0,1}^L is secure against parity \
    prediction"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 2.8",
      locator := "Section 2.2.3.2, pp. 20–22 (Attack Game 2.3, Definition 2.4 and Theorem 2.8, \
        p. 21)" }
  ]
  theorems := [
    Cslib.Crypto.Encryption.DEMOneTimeKeyINDCPAOn.negligible_parityWordAdvantage
  ]
  scope := "The cipher is a family of randomized encryption algorithms encryptSym n k m on bit \
    words at security parameter n, with no system parameter. Its key is a uniform keyLen n-bit \
    word: the book's uniformly sampled key space K is the set of keyLen n-bit words. Its message \
    space is M = {0,1}^L with L = msgLen n. The premise is semantic security (Attack Game 2.1 \
    and Definition 2.2, p. 16) against uniform strict PPT two-stage adversaries, for exactly the \
    challenge pairs in M: DEMOneTimeKeyINDCPAOn with the predicate that both messages have \
    msgLen n bits. A pair outside M makes both experiments output 0, and nothing is assumed \
    about messages of other lengths. Encryption need not be efficient or correct, since the \
    proof uses neither, and decryption is not modeled. Conclusion: every uniform strict PPT \
    predictor A, given 1ⁿ and c ← E(k, m) for a uniform m ∈ {0,1}^(msgLen n), has negligible \
    Parityadv[A, E] = |Pr[b̂ = parity(m)] − 1/2| (parityWordAdvantage; Attack Game 2.3 and \
    Definition 2.4, p. 21). The theorem assumes 1 ≤ msgLen n for every n, which the book leaves \
    implicit: at L = 0 the parity is constant and the conclusion fails, as the module's tests \
    check. It also assumes msgLen is computable in polynomial time in unary. This follows from \
    the book's requirements: M is efficiently recognizable (Definition 2.10, p. 31) and its \
    words have polynomially bounded length (Definition 2.9, p. 30), so L is found by testing \
    0^i ∈ M up to that bound. The reduction parityWordToDEMAdversary is the book's B: it draws \
    a uniform m₀, sets m₁ = m₀ ⊕ (0^(L−1) ‖ 1) and outputs 1 iff b̂ = parity(m₀). \
    isPPT_parityWordToDEMAdversary certifies it uniform strict PPT, and \
    parityWordAdvantage_eq_half_mul_demKeyGameOn, in the same module, is the proof's equation \
    Parityadv[A, E] = SSadv[B, E]/2 at each n. The tests check a cipher that pads \
    msgLen n-bit messages and sends other messages in the clear: the theorem applies to it, \
    and it fails the equal-length notion DEMOneTimeKeyWordINDCPA. \
    parityAdvantage_eq_half_mul_advantage_parityReduction, in the same module, is the equation \
    for one cipher over BitString L with any key sampler and is not listed."

register_result "deterministic-cipher-not-indcpa" where
  title := "Deterministic and zero-expansion symmetric ciphers are not CPA-secure"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Example 5.1; Exercise 5.10(a)",
      locator := "Section 5.3, p. 182; Section 5.8, p. 211" }
  ]
  theorems := [
    Cslib.Crypto.SymmetricCipher.not_indcpa_of_deterministic,
    Cslib.Crypto.SymmetricCipher.advantage_cpaGame_detCPAAdversary,
    Cslib.Crypto.SymmetricCipher.not_indcpa_of_ciphertext_length_eq
  ]
  scope := "SymmetricCipher on n-bit plaintexts at security parameter n (Section 5.3, Attack \
    Game 5.2 and Definition 5.2, against uniform strict oracle-PPT distinguishers, with the \
    scheme's own keyGen and encrypt evaluated exactly and decryption completeness \
    decrypt_encrypt). In not_indcpa_of_deterministic and advantage_cpaGame_detCPAAdversary \
    (Example 5.1), encryption is assumed deterministic only on 0^n under supported keys from some \
    n₀ onward, and the certified two-query distinguisher detCPAAdversary ctBound queries (0^n, \
    1^n) and (0^n, 0^n) for n ≥ 1 with replies truncated to ctBound n bits (the identity on \
    supported ciphertexts under CiphertextLengthLE), achieving CPA advantage 1 and refuting \
    INDCPA. In not_indcpa_of_ciphertext_length_eq (Exercise 5.10(a)), zero ciphertext expansion \
    (CiphertextLength n n on supported keys and n-bit messages) forces deterministic encryption by \
    finiteness of {0,1}^n and therefore refutes INDCPA. Malformed query pairs in cpaGame are \
    answered with []. Outside check: PR #6337, review 5951220815."

register_result "indcpa-no-repeating-ciphertexts" where
  title := "CPA-secure symmetric ciphers have negligible probability of repeating ciphertexts"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 5.12", locator := "Section 5.8, p. 211" }
  ]
  theorems := [
    Cslib.Crypto.SymmetricCipher.INDCPA.negligible_repeatCiphertextGame,
    Cslib.Crypto.SymmetricCipher.succProbability_repeatCiphertextGame_le_two_mul_advantage
  ]
  scope := "SymmetricCipher on n-bit plaintexts at security parameter n (equal-length messages of \
    size |M| = 2^n ≥ 2 for n ≥ 1, with uniform message generation via fair-coin \
    BitString.sampleList n). In repeatCiphertextGame, any adversary A with polymorphic encodable \
    return type α queries E.ciEncryptionOracle n k on n-bit plaintexts (non-n-bit queries return \
    [] without logging) and wins iff two logged ciphertexts are equal. The reduction \
    repeatToCPAAdversary ctBound A is certified IsOraclePPT encBool from IsOraclePPT encOut A, \
    truncates oracle replies to ctBound n bits (the identity on supported ciphertexts under \
    CiphertextLengthLE), and proves RepeatAdv[A, E] ≤ 2 · CPAadv[B, E] for all n ≥ 1 and \
    negligible winning probability under E.INDCPA. Outside check: PR #6337, review 5951220815."

register_result "list-cdh-guessing" where
  title := "Under CDH, no efficient adversary lists the Diffie–Hellman value among polynomially \
    many candidates"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "guessing argument for protocol PAKE₁ (unnumbered)",
      locator := "Section 21.11.4, p. 908" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.CDH.negligible_listCDHGame
  ]
  scope := "Over a PrimeOrderGroupFamily with group parameters drawn from a setup law, under the \
    CDH assumption F.CDH setup (Attack Game 10.5 and Definition 10.7, pp. 409–410); the setup \
    law need not be efficiently samplable, and the assumption is Boneh–Shoup's when it is. The \
    book claims that an eavesdropper on PAKE₁ makes a relevant random-oracle query \
    (pw′, id_P, id_Q, u, v, w′), one with w′ = [u, v], only with negligible probability. Its \
    reduction gives u and v to the eavesdropper, answers the oracle from a table, collects the \
    values w′ of the queries of that form and outputs one of them at random. Here PAKE₁, the \
    passwords and the random oracle are not modelled, and the adversary returns the candidate \
    values itself: given a·g and b·g for uniform exponents a and b, it outputs a list of group \
    elements and wins listCDHGame when (a·b)·g is among the first Q n entries. An eavesdropper \
    that answers its own oracle queries by lazy sampling is such an adversary. Q is any bound \
    computable in polynomial time in unary; for an efficiently samplable setup law a strict PPT \
    adversary's lists have polynomial length, so Q can cover them, where the book states no \
    bound. Adversaries return typed group elements and are uniform strict PPT on their \
    encodings (ListCDHAdversary.IsPPT), the convention of CDH. Conclusion: every such adversary \
    wins with negligible probability. The reduction listCDHToCDHAdversary draws a position \
    below Q n with n fair coins (sampleModIndex) instead of choosing among the collected \
    entries, outputs g past the end of the list, and is certified strict PPT \
    (isPPT_listCDHToCDHAdversary). succProbability_listCDHGame_le, in the same module, bounds \
    the success probability by Q n times the reduction's CDH success probability plus \
    Q n/2^(width n), for a reduction drawing width n coins. Its factor Q n is the bound \
    CDHadv[Bcdh, G] ≥ Pr[Z]/Q, (11.12) in the proof of Theorem 11.4 (Section 11.5.1, \
    pp. 447–448), which uses the same guessing step; the added term is the cost of the fair \
    coins."

register_result "baby-step-giant-step" where
  title := "Baby-step/giant-step computes discrete logarithms in a generic cyclic group of order \
    q with at most 2⌊√(q − 1)⌋ group operations"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "baby-step/giant-step algorithm (unnumbered)",
      locator := "Section 16.1.1, pp. 682–683; Section 16.3, p. 693" }
  ]
  theorems := [
    Cslib.Crypto.GenericGroup.babyStepGiantStep_sqrt,
    Cslib.Crypto.GenericGroup.evalPure_babyStepGiantStep,
    Cslib.Crypto.GenericGroup.isQueryBounded_babyStepGiantStep,
    Cslib.Crypto.GenericGroup.queriesSatisfy_babyStepGiantStep,
    Cslib.Crypto.GenericGroup.evalPure_groupAnswer_babyStepGiantStep
  ]
  scope := "babyStepGiantStep m n is a deterministic program over the group oracle of the \
    generic group model of Section 16.3 (p. 693), given the labels L(1) and L(α), with m baby \
    and n giant labels. The bounds count group-oracle queries, the book's group operations, not \
    running time: every query is a product of two labelled elements \
    (queriesSatisfy_babyStepGiantStep), and table lookups, the search and arithmetic on indices \
    are not counted, as in the book's count. evalPure_babyStepGiantStep: for every q ≠ 0, prime \
    or not as in Section 16.1.1, every injective labeling L, every α and all m, n with q ≤ mn, \
    the output is α. isQueryBounded_babyStepGiantStep: at most m + n − 2 queries on every run, \
    whatever the oracle answers. The program stores all m baby and n giant labels, so it does \
    not realize the book's time/space trade-off, which keeps a table of size O(m); no space \
    bound is claimed. babyStepGiantStep_sqrt: at the book's m = n = ⌈√q⌉, written \
    Nat.sqrt (q − 1) + 1, the output is α after at most 2⌊√(q − 1)⌋ < 2√q queries, the book's \
    'about 2q^(1/2) group operations in the worse case'. \
    evalPure_groupAnswer_babyStepGiantStep: run on a ZMod q-module with g of order q, on g and \
    α·g, the output is α. Deviations: the giant steps add the label of m instead of multiplying \
    by g^(−m), so no inversion is used, and all giant labels are computed before the search, \
    which leaves the worst case unchanged. The book's O(q^(1/2)) running time with an \
    associative array is not formalized."

register_result "recursive-discrete-log" where
  title := "Algorithm RDL computes discrete logarithms in a cyclic group of order q^e, generated \
    by the given base, with at most e·T + 6e⌈log₂ e⌉⌈log₂ q⌉ group operations, given a base \
    case of T operations"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Algorithm RDL (unnumbered)",
      locator := "Section 16.1.2.1, pp. 684–685" }
  ]
  theorems := [
    Cslib.Crypto.GenericGroup.evalPure_recursiveDlog,
    Cslib.Crypto.GenericGroup.isQueryBounded_recursiveDlog,
    Cslib.Crypto.GenericGroup.queriesSatisfy_recursiveDlog,
    Cslib.Crypto.GenericGroup.evalPure_groupAnswer_recursiveDlog
  ]
  scope := "recursiveDlog base q e g u is Algorithm RDL over the group oracle of the generic \
    group model (Section 16.3, p. 693), with f = ⌊e/2⌋ and a base-case program base for order \
    q. It computes u/g^β as u·g^(q^e − β) by repeated squaring, so every query is a product of \
    two labels when those of base are (queriesSatisfy_recursiveDlog). The bounds count \
    group-oracle queries, the book's group operations, not running time; integer arithmetic on \
    exponents is not counted. isQueryBounded_recursiveDlog: for q ≥ 2, e ≥ 1 and a base case of \
    at most T queries, at most e·T + 6e⌈log₂ e⌉⌈log₂ q⌉ queries on every run, the book's \
    O(e·T_base + e log e log q) with this library's constants. evalPure_recursiveDlog: in a \
    group of order n given by an oracle that multiplies the labels of L, for s of order q^e \
    (e ≥ 1) and a base case correct on every element of order q, the output on L(s) and L(αs) \
    is α for every α < q^e, so logarithms are taken in the cyclic subgroup generated by s, the \
    book's G; q need not be prime, as in the book. \
    evalPure_groupAnswer_recursiveDlog: on a ZMod n-module with g of order n = q^e and \
    baby-step/giant-step as the base case, the output on g and α·g is α. The Pohlig–Hellman \
    algorithm for several primes (Algorithm PH, Section 16.1.2.2) is not formalized."

register_result "cdh-inverse-order-negligible" where
  title := "Under CDH, the inverse group order 1/q is negligible"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "remark that 1/q is negligible under CDH (unnumbered)",
      locator := "Section 12.6.2, p. 500" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.CDH.negligible_inv_order
  ]
  scope := "Over a PrimeOrderGroupFamily along a deterministic schedule d of group parameters, \
    one group d n of prime order q(d n) for each security parameter n: if F.CDH holds for the \
    point-mass setup law at d n (Attack Game 10.5 and Definition 10.7, pp. 409–410), then \
    n ↦ 1/q(d n) is negligible. The book states this in passing while showing that the \
    multiplicative ElGamal scheme E_a is 1/q-unpredictable. In the book a negligible value is a \
    negligible function of the security parameter (Section 2.3.4, p. 35), so q is read as a \
    function of n. The assumption is Boneh–Shoup's when d is computable in polynomial time; the \
    theorem needs no condition on d and no lower bound on the orders. The proof applies CDH to \
    the adversary that always outputs the identity, which is certified strict PPT and wins \
    whenever a = 0, so with probability at least 1/q. For a setup law that samples the group, \
    CDH.negligible_expected_inv_order, in the same module, states that the expected inverse \
    order is negligible, and DDH.negligible_expected_inv_order states the same under DDH; the \
    module labels both original, and they are not listed here."

register_result "elgamal-one-way-cdh" where
  title := "Multiplicative ElGamal is one-way under CDH"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "one-wayness of multiplicative ElGamal under CDH (unnumbered)",
      locator := "Section 12.6.2, pp. 499–500; Attack Game 12.6 and Definition 12.5, p. 495" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.CDH.elGamal_oneWay,
    Cslib.Crypto.PrimeOrderGroupFamily.isPPT_elGamalOWToCDHAdversary,
    Cslib.Crypto.PrimeOrderGroupFamily.advantage_elGamalOWProbGame_cdhGame_le,
    Cslib.Crypto.owAdvantage_elGamalExplicitCoinPKE_eq_cdhAdvantage
  ]
  scope := "Over a PrimeOrderGroupFamily with any setup law setup (which need not be efficiently \
    samplable; the assumption is the book's when an efficient system parameterization algorithm \
    samples it, Definition 10.9, p. 413), the scheme at security parameter n and group d is \
    elGamalProbExplicitCoinPKE n d, written additively over F.Carrier d: key generation and \
    encryption draw their exponents from (Nat.cast : ℕ → ZMod q) <$> sampleExp n d (certified \
    strict PPT via isPPTOn_elGamalKeyGenProb and isPPTOn_elGamalEncryptProb, which realize it on \
    encoded group elements by eval_fst_elGamalKeyGenProb and eval_elGamalEncryptProb_encode), \
    and decryption is correct by elGamalExplicitCoinPKEWith_correct. In Attack Game 12.6 \
    (elGamalOWProbGame, p. 495), the challenge message is drawn from sampleGroupElem n d \
    (certified strict PPT via isPPTOn_encode_sampleGroupElem). Typed adversaries A : \
    ElGamalOWAdversary read (1^n, d, u, v, y) and write an encoded group element in uniform \
    strict PPT (ElGamalOWAdversary.IsPPT, matching CDHAdversary.IsPPT; a word-level predicate \
    would need a group decoder, which a general PrimeOrderGroupFamily lacks). The reduction \
    elGamalOWToCDHAdversary A draws y ← sampleGroupElem n d, runs A on u and (v, y), and outputs \
    y − x (computed on encodings via decodeElGamal with secret key 1), certified strict PPT by \
    isPPT_elGamalOWToCDHAdversary. Deviation from Definition 2.8 (p. 30, negligible runtime \
    overflow): strict fair-coin sampleExp sampling adds 3/2^n from the challenger's three draws \
    and 1/2^n from the reduction's draw, giving Game.advantage ≤ 4/2^n \
    (advantage_elGamalOWProbGame_cdhGame_le) and negligible success under F.CDH setup \
    (CDH.elGamal_oneWay); owAdvantage_elGamalExplicitCoinPKE_eq_cdhAdvantage gives the exact \
    fixed-group equality under uniform exponents."

register_result "elgamal-unpredictable-cdh" where
  title := "Multiplicative ElGamal is (1/q + 1/2^n)-unpredictable, and unpredictable under CDH"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "1/q-unpredictability and unpredictability under CDH of multiplicative ElGamal \
        (unnumbered)",
      locator := "Section 12.6.2, p. 500; Definition 12.6, p. 495" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.CDH.elGamal_unpredictable,
    Cslib.Crypto.PrimeOrderGroupFamily.epsilonUnpredictable_elGamalProbExplicitCoinPKE,
    Cslib.Crypto.epsilonUnpredictable_elGamalExplicitCoinPKE
  ]
  scope := "Unpredictability is Definition 12.6 (p. 495): PKE.EpsilonUnpredictable and \
    Encryption.Unpredictable (where rejected ciphertexts are unconstrained; multiplicative \
    ElGamal never rejects and is correct by elGamalExplicitCoinPKEWith_correct, so this agrees \
    with the book's default-message convention). Over any fixed ZMod q-module G with injective \
    β ↦ β·g and exact uniform coins (elGamalExplicitCoinPKE q g), the first ciphertext component \
    β·g determines β, giving exact 1/q-unpredictability \
    (epsilonUnpredictable_elGamalExplicitCoinPKE). Over a PrimeOrderGroupFamily at security \
    parameter n and group d, the fair-coin scheme elGamalProbExplicitCoinPKE n d (realized on \
    encoded group elements by elGamalKeyGenProb, elGamalEncryptProb and elGamalDecryptDet) draws \
    its encryption coins via sampleExp n d, relaxing exact 1/q (under Definition 2.8's negligible \
    runtime-overflow model, p. 30) to (1/q + 1/2^n)-unpredictability \
    (epsilonUnpredictable_elGamalProbExplicitCoinPKE). Along a deterministic group schedule d \
    (fixing one scheme per security parameter as Encryption.Unpredictable requires; the CDH \
    assumption is the book's when d is computable in polynomial time), F.CDH at the point-mass \
    setup makes 1/q negligible (CDH.negligible_inv_order), so (elGamalProbExplicitCoinPKE n \
    (d n)).toPKE is unpredictable (CDH.elGamal_unpredictable). Strong unpredictability on all \
    public-key words (§21.4.1) is in elgamal-strongly-unpredictable-ciphertexts."

open Cslib.Crypto.PrimeOrderGroupFamily in
register_result "dlog-self-reduction-iterated" where
  title := "If an efficient algorithm finds the discrete logarithm of a random element with \
    inverse-polynomial probability, an efficient algorithm finds every discrete logarithm with \
    negligible failure probability"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "remark after Theorem 10.2 on iterating the random self-reduction (unnumbered)",
      locator := "Section 10.5.1, p. 412; Theorem 10.2 and its proof, pp. 411–412" }
  ]
  theorems := [
    negligible_dlSelfReduceRetryAdversary_error,
    isPPTOn_dlSelfReduceRetryAdversary_invEps,
    eq_nil_or_encode_smul_eq_of_mem_support_dlSelfReduceRetryAdversary
  ]
  scope := "The group is fixed for each security parameter, as footnote 1 on p. 411 fixes it: \
    any sequence d of parameters of a PrimeOrderGroupFamily, the group d n having prime order q \
    and generator g. The adversary is a word-level discrete-logarithm adversary, reading 1^n, \
    d n and an encoded element and writing the exponent in binary, read modulo q, as in \
    DiscreteLog. Hypotheses: for all large n it wins discreteLogGame with the point-mass setup \
    at d n, that is on a uniform element of d n (the book's ε), with probability at least \
    1/invEps n > 0, where invEps is computable in polynomial time in unary; when 1/ε is \
    poly-bounded, a polynomial above it serves. dlSelfReduceRetryAdversary makes \
    n·(2·invEps n) attempts of the algorithm B of Theorem 10.2 (mask the input by σ·g, run the \
    adversary, subtract σ, test the answer) and returns the first answer that passes, or the \
    empty word for the book's fail. Its masks come from the fair-coin sampler sampleExp, within \
    1/2^n of uniform; the doubled attempt count, against the book's n⌈1/ε⌉, absorbs that loss. \
    negligible_dlSelfReduceRetryAdversary_error: on the encoding of every sequence of elements \
    α n·g, the program fails or returns a word that does not read as α n only with negligible \
    probability. isPPTOn_dlSelfReduceRetryAdversary_invEps: it is uniform strict PPT whenever \
    the adversary is. eq_nil_or_encode_smul_eq_of_mem_support_dlSelfReduceRetryAdversary: on \
    every input word it outputs fail or a discrete logarithm of the input, Theorem 10.2's 'B \
    either outputs fail or Dlog_g(u)'. dlSelfReduceRetryAdversary_error_le_pow, in the same \
    module, bounds the error by (1/2)^n at each n at which the success probability is at least \
    1/invEps n and 1/2^n ≤ 1/(2·invEps n); under the hypotheses above both hold for all \
    sufficiently large n, so the error is at most (1/2)^n for all large n, where the book has \
    exp(−n). Theorem 10.2 itself is not part of this entry: for one fair-coin attempt the \
    module proves success at least ε − 1/2^n (le_toOuterMeasure_dlSelfReduceRetryAdversary_one), \
    and the exact ε is eval_dlSelfReduce_one_smul_some in SelfReduction.lean, which has uniform \
    masks and no cost model. discreteLog_of_worstCase, the library's formulation of the book's \
    'if it is hard in the worst case, then it must be hard on average' (p. 412), is not \
    listed."

register_result "ddh-fixed-first-coordinate-rerandomization" where
  title := "With u fixed, (v, w) ↦ (g^σ v^τ, u^σ w^τ) sends a DH-triple to a uniform DH-triple \
    and any other triple to a uniform triple, both with first coordinate u"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 10.8", locator := "Section 10.11, p. 425" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomizeLaw_real,
    Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomizeLaw_random
  ]
  scope := "In the group of any description d of a PrimeOrderGroupFamily, of prime order q with \
    generator g and written additively, where every element is a multiple of g. For u = α·g, \
    ddhFixedURerandomizeLaw draws σ and τ exactly uniformly from Z_q and outputs \
    (v*, w*) = (σ·g + τ·v, σ·u + τ·w), the book's (g^σ v^τ, u^σ w^τ); u stays fixed. \
    ddhFixedURerandomizeLaw_real, part (a): on a DH-triple (α·g, β·g, (αβ)·g) the law of \
    (v*, w*) is that of (β′·g, (αβ′)·g) for uniform β′, the uniform distribution on DH ∩ T_u \
    written by its last two coordinates. ddhFixedURerandomizeLaw_random, part (b): on a triple \
    (α·g, β·g, γ·g) with γ ≠ αβ it is that of (β′·g, γ′·g) for independent uniform β′ and γ′, \
    the uniform distribution on T_u. These are equalities of distributions in one group; the \
    exercise makes no efficiency claim. With exponents from the fair-coin sampler sampleExp, \
    the executable ddhFixedUSelfReduceDistinguisher changes any test's acceptance probability \
    by at most 2/2^n \
    (advantage_ddhFixedURerandomizeLaw_ddhFixedUSelfReduceDistinguisher_le, in the same \
    module)."

register_result "ddh-worst-case-decider" where
  title := "An efficient DDH distinguisher with inverse-polynomial advantage gives an efficient \
    algorithm that decides with negligible error whether any triple is a DH-triple"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 10.10",
      locator := "Section 10.11, p. 426; Exercises 10.8–10.9, pp. 425–426" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.negligible_ddhAmplifiedDecider_error,
    Cslib.Crypto.PrimeOrderGroupFamily.isPPT_ddhAmplifiedDecider
  ]
  scope := "Over a PrimeOrderGroupFamily along any sequence d of group parameters, the group d n \
    having prime order q and generator g, given to the algorithms as input. Hypotheses: for all \
    large n the distinguisher's advantage in the group d n (ddhAdvantage: |Pr[real] − \
    Pr[random]| for uniform exponents, Attack Game 10.6 in a fixed group) is at least \
    1/invEps n, and invEps n > 0, where invEps is computable in polynomial time in unary. The \
    exercise assumes that this absolute difference equals ε with 1/ε poly-bounded; a polynomial \
    above 1/ε serves as invEps. ddhAmplifiedDecider runs N = (n + 3)·(7·invEps n)² trials of \
    the DDH self-reduction ddhSelfReduceDistinguisher (Exercises 10.8–10.9, with exponents from \
    the fair-coin sampler sampleExp) on the input triple, on the DH-triple (0, 0, 0) and on the \
    non-DH-triple (0, 0, g), and answers according to which reference count the input's count \
    is closer to, so it need not know which probability is larger. \
    negligible_ddhAmplifiedDecider_error: on every sequence of inputs (α n·g, β n·g, γ n·g), \
    which covers every triple of elements, the probability that its answer differs from \
    [γ n = α n·β n] is negligible; this holds for any distinguisher. isPPT_ddhAmplifiedDecider: \
    the decider is uniform strict PPT whenever the distinguisher is (DDHDistinguisher.IsPPT). \
    ddhAmplifiedDecider_error_le_pow, in the same module, bounds the error by (1/2)^n at each n \
    at which the advantage is at least 1/invEps n > 0 and 3/2^n ≤ 1/(12·invEps n); under the \
    hypotheses above both hold for all sufficiently large n, so the error is at most (1/2)^n \
    for all large n. The exercise states no bound."

register_result "multi-ddh-from-ddh" where
  title := "Under DDH, the Multi-DDH (I) distributions D and R are computationally \
    indistinguishable"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 10.11",
      locator := "Section 10.11, p. 426; Definition 3.4, p. 82" }
  ]
  theorems := [
    Cslib.Crypto.PrimeOrderGroupFamily.DDH.multiDDH,
    Cslib.Crypto.PrimeOrderGroupFamily.DDH.singleSecretMultiDDH
  ]
  scope := "Over a PrimeOrderGroupFamily with group parameters drawn from a setup law, under DDH \
    for that law (Attack Game 10.6 and Definition 10.8, pp. 410–411); the setup law need not be \
    efficiently samplable, and the assumption is Boneh–Shoup's when it is. The exercise's n \
    secrets and m pairs per secret are schedules secretCount n and pairCount n, computable in \
    polynomial time in unary so that the uniform reduction knows how many to generate; zero is \
    allowed, where the exercise has positive n and m. multiDDHRealGame gives the distinguisher \
    1^n, the group parameters and secretCount n blocks (α_i·g, [(β_ij·g, (α_i β_ij)·g)]), the \
    distribution D written additively; multiDDHRandomGame replaces (α_i β_ij)·g by γ_ij·g, the \
    distribution R. All exponents are exactly uniform and independent. DDH.multiDDH: every \
    uniform strict PPT distinguisher (MultiDDHDistinguisher.IsPPT) has negligible advantage, \
    the exercise's computational indistinguishability (Definition 3.4) read asymptotically. \
    DDH.singleSecretMultiDDH is the case of one secret with count n pairs. The reductions \
    multiDDHToDDHDistinguisher and singleSecretMultiDDHToDDHDistinguisher, built from \
    Exercises 10.8–10.9 with exponents from the fair-coin sampler sampleExp, are certified \
    strict PPT (isPPT_multiDDHToDDHDistinguisher, isPPT_singleSecretMultiDDHToDDHDistinguisher). \
    advantage_multiDDHGame_le, in the same module, is the exercise's bound \
    Distadv[A, D, R] ≤ 1/q + DDHadv[B, G] with 1/q replaced by its expectation over the setup \
    law and an added sampling term 2·secretCount n·(1 + 2·pairCount n)/2^n; the expected 1/q is \
    negligible under DDH (DDH.negligible_expected_inv_order)."

register_result "malleable-encryption-not-1cca" where
  title := "A public-key scheme with an efficient transformation whose decryption reveals the \
    challenge bit is not 1CCA secure"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "malleability example with a CCA adversary of advantage 1 (unnumbered)",
      locator := "Section 12.2.1, pp. 469–470" }
  ]
  theorems := [
    Cslib.Crypto.Encryption.not_indcca2On_of_maulAdversary,
    Cslib.Crypto.Encryption.advantage_cca2GameOn_maulAdversary
  ]
  scope := "The book gives an example: the scheme E_TDF with a stream cipher, where Molly changes \
    the header of a ciphertext but not its body (p. 470), and a CCA adversary A with advantage \
    1 against any scheme that allows such a change. These theorems prove a conditional \
    criterion behind that example, for any public-key scheme (keyGen, encrypt, decrypt) on \
    words, with a message type Msg and a predicate valid that admits challenge pairs. \
    Criterion: (i) messages msg₀ and msg₁, computed from the public key in polynomial time, \
    form a pair that valid admits under every honest public key; (ii) a transformation maul \
    and a target word are computable in polynomial time; (iii) for every honest key pair and \
    every ciphertext c in the support of the encryption of msg₀ or msg₁, maul(pk, c) ≠ c, and \
    the decryption of maul(pk, c) encodes to the target exactly when c encrypts msg₁. \
    maulAdversary plays the book's A: with no Phase 1 query it submits the pair, makes the \
    single Phase 2 query maul(pk, c) and compares the reply with the target. It is certified \
    strict oracle PPT (isPPT_maulAdversary). advantage_cca2GameOn_maulAdversary states that \
    its advantage is exactly 1 at every n where (i) and (iii) hold, and \
    not_indcca2On_of_maulAdversary concludes that the scheme is not INDCCA2On valid (Attack \
    Game 12.1 and Definition 12.2, pp. 467–468, one encryption query, against uniform strict \
    oracle-PPT adversaries). Validity condition: the library's 1CCA game decrypts every word \
    other than the challenge and admits whatever pairs valid admits, whereas the source's \
    decryption queries lie in the ciphertext space C and its challenge messages lie in M and \
    have the same length. The conclusion is the source's only when the derived query \
    maul(pk, c) lies in C for every honest challenge ciphertext c, as Molly's ciphertext does, \
    and msg₀ and msg₁ are such messages; then maulAdversary is an adversary of Attack \
    Game 12.1 with advantage 1 there. The theorems do not state that condition, so each \
    application has to check it. The library applies them to ElGamal, Goldwasser–Micali and \
    Paillier encryption, so (i)–(iii) can hold."

register_result "functional-encryption-injective-null-key" where
  title := "When the null function is injective, every functional encryption scheme, the \
    cleartext scheme included, has semantic-security advantage zero"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "Remark 15.13: the zero advantage behind it; Definition 15.14 is not formalized",
      locator := "Section 15.7, p. 661" }
  ]
  theorems := [
    Cslib.Crypto.FE.advantage_ssExperiment_eq_zero_of_injective_null,
    Cslib.Crypto.FE.advantage_ssExperiment_pke_eq_zero,
    Cslib.Crypto.FE.cleartext_correct
  ]
  scope := "FE is Definition 15.13 (pp. 658–659) for one fixed scheme: typed setup, key \
    generation and encryption programs, and deterministic decryption into Option Y, where none \
    stands for both ⊥ and reject; there is no security parameter and no efficiency. \
    FE.ssExperiment is Attack Game 15.9 (pp. 660–661) with one encryption query and adaptive key \
    queries before and after it: the adversary receives mpk and the null key sk_ε, and the run \
    outputs 0 unless ε and every queried function agree on the challenge pair. \
    advantage_ssExperiment_eq_zero_of_injective_null: if F(ε, ·) is injective, every adversary, \
    with no bound on its computation, has SSadv[A, FE] = 0 against every scheme, since only \
    pairs with m₀ = m₁ are admissible. advantage_ssExperiment_pke_eq_zero is the Remark's \
    functionality: the identity key and a null key that reveals π(m), for any injective π \
    (Functionality.pke π). cleartext_correct: the Remark's scheme E(mpk, m) := m, whose key for \
    f is f and whose decryption is F(f, ·), is correct. One-wayness of π is not needed. The \
    Remark concludes that the scheme is secure under Definition 15.14, the asymptotic notion \
    for efficient schemes, which is not formalized (#4894); this entry records the zero \
    advantage on which that rests. cleartext_robust, in the same module, proves the library's \
    FE.Robust, which the book's Definition 15.15 implies but not conversely; the Remark does not \
    claim robustness."

register_result "pke-as-functional-encryption" where
  title := "A public-key scheme, as functional encryption for the identity and the null \
    function len, is correct exactly when the scheme is correct and the null key computes len"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Example 15.1, with the null key of p. 660",
      locator := "Section 15.7, pp. 659–660" }
  ]
  theorems := [
    Cslib.Crypto.PKE.toFE_correct_iff
  ]
  scope := "Functionality.pke len is (15.33) with the null identifier ε of p. 660: the identity \
    I (some ()) returns the message and ε (none) returns len(m), tagged in M ⊕ L. PKE.toFE leak \
    views a public-key scheme as a functional encryption scheme whose key for I is the secret \
    key and whose null key is public and returns leak(c). toFE_correct_iff: E.toFE leak is \
    correct for Functionality.pke len (Definition 15.13, p. 659) exactly when E is correct and \
    leak(c) = len(m) for every honest key pair and every honest encryption c of m. Typed records \
    for one fixed scheme, without security parameter or efficiency. \
    eval_ssExperiment_toFE_ofTwoStage, in the same module, matches Attack Game 15.9 for E.toFE \
    against adversaries that make no key query with the chosen-plaintext experiment of E under \
    equal len; it checks the two games against each other and is not a claim of the book."

register_result "partial-tag-encrypt-then-mac" where
  title := "Encrypt-then-MAC over a one-block PRF cipher with an unauthenticated IV loses \
    ciphertext integrity (an analogue of the randomized-CBC example)"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "unauthenticated-IV example for randomized CBC mode (unnumbered); an analogue",
      locator := "Section 9.4.1.1, pp. 368–369" }
  ]
  theorems := [
    Cslib.Crypto.not_ciphertextIntegrity_prfCipherPartialTag,
    Cslib.Crypto.not_authenticatedEncryption_prfCipherPartialTag,
    Cslib.Crypto.PseudorandomFunction.prfCipherPartialTag_counterexample
  ]
  scope := "An analogue of the book's example, not the example itself. The book applies \
    encrypt-then-MAC to randomized CBC mode and computes the tag on the body c alone, leaving \
    the IV r unauthenticated (pp. 368–369). The construction here is prfCipherPartialTag. Its \
    cipher is the one-block PRF cipher prfCipher for a keyed family F with n-bit keys, inputs \
    and outputs, computable in polynomial time: the ciphertext of an n-bit message m is \
    r ‖ (F(k, r) ⊕ m) for a uniform n-bit IV r. Its MAC is any MACScheme on n-bit messages, \
    applied to the body alone (partialTagMAC), so the IV is not authenticated. CBC mode is \
    not part of this entry, and neither is its plaintext shift m′[0] = m[0] ⊕ Δ (p. 369). \
    The adversary partialTagCIAdversary makes one encryption query, on 0^n, flips the first \
    bit of the IV and keeps the body and the tag, giving a ciphertext (r′, c, t) with r′ ≠ r \
    as on p. 368. It is certified strict oracle PPT (isOraclePPT_partialTagCIAdversary) and \
    wins with probability 1 for n ≥ 1 \
    (eval_ciOneTimeGame_prfCipherPartialTag_partialTagCIAdversary). Its query is an n-bit \
    message and its forgery has the form of an honest ciphertext of this scheme, so it also \
    wins Attack Game 9.1 for this scheme. Hence, for every such F and every MAC, with no \
    assumption, the scheme provides neither ciphertext integrity (Attack Game 9.1 and \
    Definition 9.1, pp. 358–359), nor its one-time form (Definition 9.3, p. 360), nor \
    authenticated encryption (Definition 9.2, p. 359). prfCipherPartialTag_counterexample \
    adds that when F is a PseudorandomFunction (Attack Game 4.2 and Definition 4.2, \
    pp. 132–133), the same scheme is INDCPA (Attack Game 5.2 and Definition 5.2, \
    pp. 181–182, on n-bit messages) while it lacks one-time ciphertext integrity."

register_result "fixed-length-polynomial-universality" where
  title := "Collision and difference bounds for fixed-length polynomial hashing"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 7.16(a)–(b)",
      locator := "v0.6, printed p. 281; Hfpoly in §7.2.1, equation (7.5), p. 257" }
  ]
  theorems := [
    Cslib.Probability.isUniversalHash_coeffPolyHash,
    Cslib.Probability.isDeltaUniversalHash_mul_coeffPolyHash
  ]
  scope := "For length-n coefficient vectors and an exactly uniform field element, the \
    collision probability is at most (n − 1)/|F|. Multiplying the evaluation by the key bounds \
    the probability of any specified difference by n/|F|. Both statements quantify over \
    distinct vectors, extend from prime fields to all finite fields, and apply pointwise in n \
    without a growth condition. The zero-length vector has no distinct partner."

register_result "ghash-gcm-length-block-xor-duf" where
  title := "GHASH on the bit-length version of GCM's line (∗) input, zero-padded with its \
    length block, is an ℓ/2^128-XOR-DUF for inputs of at most ℓ blocks, the length block \
    included"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023,
      theorem := "GHASH (9.18) with the length fields of line (∗) keeps the XOR-DUF property \
        (unnumbered)",
      locator := "Section 9.7, pp. 381–382; XOR-DUFs: Remark 7.3, p. 269" }
  ]
  theorems := [
    Cslib.Crypto.isDeltaUniversalHash_ghashBits_gcmHashInput
  ]
  scope := "GHASH is (9.18), z[0]·k^v + ⋯ + z[v − 1]·k, evaluated in any field F with an \
    additive bijection e between F and {0,1}^128; GF(2^128) with the modulus \
    X^128 + X^7 + X^2 + X + 1 and the standard's bit order is such a field but is not \
    constructed. The key is uniform in {0,1}^128 (in GCM it is E(k, 0^128)). gcmHashInput d c \
    is the bit-length version of the input of line (∗): d and c padded with zeros to 128-bit \
    blocks, then one block holding their lengths in bits as two 64-bit numbers, where the \
    book's length fields count bytes; a one-byte input contributes 8 to the length field here \
    and 1 in the book. For any family of inputs x determined by the \
    pair (d x, c x), with both lengths below 2^64 and at most ℓ blocks hashed, the length block \
    included, GHASH is an ℓ/2^128-XOR-DUF in the sense of Remark 7.3: for x ≠ x′ and every \
    δ, Pr_k[GHASH(k, x) ⊕ GHASH(k, x′) = δ] ≤ ℓ/2^128, where ℓ counts the length block among \
    the blocks. Deviations: the bit lengths separate arbitrary bit strings after padding, which \
    byte lengths would not; the book's limit ℓ = 2^32 − 1 on the number of blocks keeps both \
    lengths below 2^64 bits; and the book gives no ε for GHASH, while Remark 7.4 gives \
    (ℓ + 1)/2^n for H_xpoly, which has the extra leading term k^(v+1). Without the length \
    block GHASH is not even universal on inputs of at most ℓ blocks, since [] and [0] collide \
    under every key (not_isUniversalHash_ghash, in the same module, not listed). Only the hash \
    is formalized, not GCM's encryption or its AEAD security."

register_result "rsa-half-predicate-inversion" where
  title := "Baby Bleichenbacher: an oracle for the half predicate inverts RSA"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Exercise 12.21(a)–(b)",
      locator := "Section 12.11, pp. 519–520" }
  ]
  theorems := [
    Cslib.Crypto.lsbRecover_map_decide_lt_two_mul,
    Cslib.Crypto.lsbInverter_halfToLSBPredictor,
    Cslib.Crypto.succProbability_rsaInversionGame_halfToLSBPredictor
  ]
  scope := "Part (a), lsbRecover_map_decide_lt_two_mul: for an odd modulus N ≤ 2^m and x < N, \
    the values of P_x(r) = [x·r mod N > N/2], written N < 2·(x·r mod N), at \
    r = 2^0, …, 2^(m−1) determine x, and lsbRecover computes x from them; with m = N.size these \
    are about log₂ N points. lsbRecover runs in polynomial time \
    (computableInPolyTime_lsbRecover, in RSALeastSignificantBit.lean). The source's modulus is \
    an RSA modulus, hence odd; the theorem needs oddness, since modulo 6 the predicates P_0 and \
    P_3 agree everywhere. Part (b): H is an oracle that, on each RSA image w^e mod N, answers \
    whether w > N/2. lsbInverter (halfToLSBPredictor H) asks H about 2^(k·e)·y mod N, the RSA \
    images of 2^k·w mod N, for k < N.size in order, and returns lsbRecover of the answers \
    (lsbInverter_halfToLSBPredictor): part (a) at the points r = 2^k. \
    succProbability_rsaInversionGame_halfToLSBPredictor: if every modulus in the support of \
    gen n is odd and H answers correctly on every RSA image, the inverter wins the RSA \
    inversion game (Attack Game 10.3, pp. 404–405, with keys from any law on RSADesc and a \
    uniform challenge in Z_N) with probability 1; it recovers every e-th root \
    (eval_lsbInverter with eval_halfToLSBPredictor). H is passed as a function, not as an \
    oracle channel with a query bound, so efficiency is stated relative to H: the inverter is \
    PPT whenever H is (isPPT_halfToLSBPredictor with isPPT_lsbInverter), and its N.size queries \
    and polynomial-time recovery are explicit. \
    RSAOneWay.not_frequently_alwaysCorrect_halfPredictor, in the same module, is a hardness \
    corollary that is not part of the exercise and is not listed."

register_result "arora-barak-expected-time-zpp" where
  title := "Expected-polynomial-time zero-error computation equals RP ∩ coRP"
  topic := "randomized complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 7.8",
      locator := "Section 7.3 (printed p. 121, PDF p. 137)" }
  ]
  theorems := [Cslib.Complexity.iUnion_ZTIME_pow_eq_RP_inter_coRP]
  scope := "The draft defines ZPP as the union of expected-time classes ZTIME(n^d). \
    The Lean class uses one closed fair-coin machine, almost-sure termination with the correct \
    answer, and polynomial expected runtime in the encoded input length. \
    Arbitrary injective input encodings. Outside check: PR #6144, review 5938376225."

register_result "goldreich-xsat-promise-np-conp" where
  title := "xSAT belongs to both promise-NP and promise-coNP"
  topic := "promise problems"
  sources := [
    { paper := Goldreich2006DraftR1, theorem := "Exercise 2.36(1)",
      locator := "Chapter 2 (printed p. 114, PDF p. 139)" }
  ]
  theorems := [Cslib.Complexity.xSAT_mem_PromiseNP_inter_promiseClass_coNP]
  scope := "Pairs of CNFs under encPair encCNF encCNF. The promise is that exactly one \
    formula is satisfiable, and the yes case is when it is the first. Each promise class \
    requires a separating language in the corresponding ordinary class. \
    Outside check: PR #6169, review 5939821895."

register_result "goldreich-pairwise-independent-hitting" where
  title := "Pairwise independent samples hit dense sets"
  topic := "pseudorandomness"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 7.23",
      locator := "Chapter 7 (printed p. 310, PDF p. 46)" }
  ]
  theorems := [
    Cslib.Probability.IsPairwiseIndependentHash.min_mul_div_two_le_dens_filter_exists_apply_mem,
    Cslib.Probability.IsPairwiseIndependentHash.three_quarters_mul_le_dens_filter_exists_apply_mem
  ]
  scope := "For a uniform finite seed, any m distinct positions with uniform pairwise \
    independent outputs and any target of density p, the probability of at least one hit is \
    at least min(m p, 1)/2, and at least 3 m p/4 when 2 m p ≤ 1. \
    Outside check: PR #6152, review 5938810997."

register_result "goldreich-small-bias-linear-codes" where
  title := "Small-bias sample spaces correspond to balanced binary linear codes"
  topic := "pseudorandomness"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 8.41",
      locator := "Chapter 8 (printed pp. 380–381, PDF pp. 116–117)" }
  ]
  theorems := [
    Cslib.BitString.sampleCode_ofCode,
    Cslib.BitString.sampleCode_injective,
    Cslib.BitString.isSmallBias_map_iff_hammingDist_sampleCode
  ]
  scope := "The linear encoding maps a message to its parity against each sample. For any \
    nonempty finite seed set of size N, ε-bias of the uniform seed's output is equivalent to \
    distances between the encodings of distinct messages lying in [(1−ε)N/2, (1+ε)N/2]. \
    The statement concerns the output distribution. Outside check: PR #6167, review 5939796761."

register_result "goldreich-ip-cook-reduction" where
  title := "IP is closed under polynomial-time Cook reductions"
  topic := "interactive proofs"
  sources := [
    { paper := Goldreich2007DraftR5, theorem := "Exercise 9.2(2)",
      locator := "Chapter 9 (printed p. 445, PDF p. 63)" }
  ]
  theorems := [Cslib.Complexity.PolyTimeTuringReducible.mem_IP]
  scope := "Adaptive polynomial-time Turing reductions to a bitstring language in IP. \
    The complement-membership hypothesis in the exercise is redundant. Lean uses \
    completeness 2/3 and soundness 1/3, equivalent to the perfectly complete class. \
    Outside check: PR #6158, review 5939165280."

register_result "goldreich-gap-linear-equations-np-hard" where
  title := "Approximating the maximum satisfied fraction of binary linear equations is NP-hard"
  topic := "hardness of approximation"
  sources := [
    { paper := Goldreich2007DraftR5, theorem := "Exercise 10.5",
      locator := "Chapter 10 (printed p. 496, PDF p. 114)" }
  ]
  theorems := [Cslib.Complexity.exists_GapLin_npHard, Cslib.Complexity.GapLin_npHard]
  scope := "For some constants 1/2 < s < L < 1, distinguishing systems over GF(2) with \
    optimum at least L from those with optimum strictly below s is NP-hard under \
    polynomial-time many-one reductions. The concrete witness has L = 4/7 and \
    s = (4/7)(1 − 1/(6·2^77)). Equations count with multiplicity under XORSAT.encoding. \
    Outside check: PR #6157, review 5939142909."

register_result "goldreich-countably-many-computable-functions" where
  title := "There are only countably many computable bitstring functions"
  topic := "computability"
  sources := [
    { paper := Goldreich2006DraftR1, theorem := "Theorem 1.4",
      locator := "Section 1.2.3 (printed p. 29, PDF p. 54)" }
  ]
  theorems := [Turing.MultiTapeTM.countable_setOf_isComputable_and_mk_eq_continuum]
  scope := "Total functions from bit strings to bit strings. The functions computable by a \
    native deterministic multitape Turing machine form a countable set, while the set of all \
    such functions has cardinality continuum. Outside-fleet clearance: \
    https://github.com/cslib-community/cslib-frontier/pull/6080#pullrequestreview-5935499657. \
    Approval: \
    https://github.com/cslib-community/cslib-frontier/pull/6080#pullrequestreview-5935757026. \
    The official draft locator was checked in \
    https://github.com/cslib-community/cslib-frontier/pull/6473#pullrequestreview-5959473706."

register_result "plaisted-greenbaum-correctness" where
  title := "Plaisted–Greenbaum: the polarity-aware clause form is equisatisfiable"
  topic := "propositional logic"
  sources := [
    { paper := PlaistedGreenbaum1986, theorem := "Theorem 1, Lemma 1, Theorem 2 and Corollary",
      locator := "§1, p. 294 (construction); p. 295 (Theorem 1); p. 297 (Lemma 1, Theorem 2, \
        Corollary)" }
  ]
  theorems := [
    Cslib.Logic.PL.Proposition.eval_of_eval_plaistedGreenbaumCNF,
    Cslib.Logic.PL.Proposition.eval_plaistedGreenbaumCNF_tseitinExtend,
    Cslib.Logic.PL.Proposition.satisfiable_plaistedGreenbaumCNF_iff
  ]
  scope := "Propositional correctness only. Inputs are arbitrary propositions over any atom \
    type with Boolean atom assignments; the deterministic construction asserts the root \
    positively, flips polarity in implication antecedents and gives equal subformulas one \
    variable. Every model of the clauses restricts to a model of the proposition, every \
    model of the proposition extends (by evaluating subformulas) to a model of the clauses, \
    and the two are equisatisfiable; no other premise is assumed. Conventions differ from the \
    paper: CNF is a list of clauses that may repeat, there are no quantifiers or \
    equivalences, and falsum is added (negation is implication to falsum). The size bound of \
    2 · A.size + 1 clauses and the non-uniqueness of the extension are separate results and \
    are not part of this entry. Outside check: PR #6181, review 5948254834."

register_result "abstract-dpll-termination" where
  title := "Abstract Basic DPLL terminates"
  topic := "SAT algorithms"
  sources := [
    { paper := NieuwenhuisOliverasTinelli2006, theorem := "Theorem 2.10",
      locator := "authors' manuscript, printed p. 14" }
  ]
  theorems := [Cslib.Algorithms.Lean.CDCL.wellFounded_basicStep]
  scope := "Propositional list CNFs over ℕ, from the initial state with the empty trail. Basic \
    DPLL is UnitPropagate, Decide, Fail and Backjump with the side conditions of Definition 2.4. \
    Stated as well-foundedness of the converse Basic DPLL step relation on states reachable by \
    DPLL with learning, which includes every state reachable by Basic DPLL. The proof uses a \
    single natural-number measure in place of the source's lexicographic order."

register_result "abstract-dpll-learning-termination" where
  title := "Abstract DPLL with learning terminates without infinite Learn/Forget stretches"
  topic := "SAT algorithms"
  sources := [
    { paper := NieuwenhuisOliverasTinelli2006, theorem := "Theorem 2.11",
      locator := "authors' manuscript, printed p. 15" }
  ]
  theorems := [Cslib.Algorithms.Lean.CDCL.wellFounded_learnOrForget_basicStep]
  scope := "DPLL with learning is Basic DPLL with Learn and Forget (Definition 2.5); clause sets \
    are lists, so Learn prepends a clause and Forget removes one occurrence. Forget uses the \
    entailment of §2.1, by partial models; Backjump and Learn use entailment by total \
    assignments, which the §2.1 entailment implies, so every step of the source is a step here. \
    A derivation with no \
    infinite subderivation of Learn and Forget steps is a sequence of moves, each finitely many \
    Learn and Forget steps followed by a Basic DPLL step; the theorem is the well-foundedness of \
    these moves from the initial state."

register_result "abstract-dpll-learning-correctness" where
  title := "Final states of abstract DPLL with learning decide satisfiability"
  topic := "SAT algorithms"
  sources := [
    { paper := NieuwenhuisOliverasTinelli2006, theorem := "Theorem 2.12",
      locator := "authors' manuscript, printed p. 15" }
  ]
  theorems := [Cslib.Algorithms.Lean.CDCL.final_of_reachable]
  scope := "For a propositional list CNF φ over ℕ and a state reachable from the initial state \
    by DPLL with learning (Basic DPLL, Learn and Forget), if no Basic DPLL step applies then the \
    state is fail exactly when φ is unsatisfiable, and otherwise the trail is a model of φ in the \
    sense of §2.1: every clause of φ has a literal on the trail. The total assignment that makes \
    the trail's literals true, and the others false, is then a model as well. Forget uses the \
    §2.1 entailment, by partial models, which this conclusion needs: with entailment by total \
    assignments, Forget could remove the tautology b ∨ ¬b from a, b ∨ ¬b and end at the trail a. \
    Backjump and Learn use entailment by total assignments, which the §2.1 entailment implies, \
    so every step of the source is a step here."

register_result "anchoring-classical-and-entangled-values" where
  title := "Classical and entangled values after anchoring a two-prover game"
  topic := "nonlocal games"
  sources := [
    { paper := BavarianVidickYuen2022, theorem := "Lemma 1.2",
      locator := "arXiv:1509.07466v2, printed p. 3 (anchoring in Definition 1.1)" }
  ]
  theorems := [
    Cslib.PCP.TwoProverGame.value_anchored,
    Cslib.PCP.TwoProverGame.quantumValue_anchored
  ]
  scope := "Anchoring replaces each player's question independently with probability α and \
    accepts if either question is replaced. For finite games with nonempty answer alphabets, \
    the classical and entangled rejection gaps both scale by (1 − α)², including α = 0 and α = 1. \
    Entangled value is the supremum over finite-dimensional tensor strategies with arbitrary \
    local POVMs. The strategy maps preserve both local dimensions."

register_result "bvy-anchored-noisy-reveal-laws" where
  title := "Conditional independence and the anchored marginal of the noisy reveal"
  topic := "nonlocal games"
  sources := [
    { paper := BavarianVidickYuen2022, theorem := "Claims 4.1–4.2",
      locator := "arXiv:1509.07466v2, §4.1, printed pp. 11–12" }
  ]
  theorems := [
    Cslib.PCP.AnchoredDependency.conditionalSnd_messagePair,
    Cslib.PCP.AnchoredDependency.leftLaw_apply,
    Cslib.PCP.AnchoredDependency.rightLaw_apply,
    Cslib.PCP.AnchoredDependency.map_snd_leftLaw,
    Cslib.PCP.AnchoredDependency.map_snd_rightLaw,
    Cslib.PCP.AnchoredDependency.map_snd_law
  ]
  scope := "For any original joint question PMF, the weighted point masses factor into the message \
    mass and two local conditional laws. The factorization expresses independence at supported \
    messages. For either designated player, forgetting the message recovers the anchored question \
    law, including anchor rates zero and one. Agreement of the left-message conditional with \
    the original anchored conditional assumes a supported message and an interior anchor rate."

register_result "bvy-anchored-conditioning-bounds" where
  title := "Movement of free trials and question resampling after checked wins"
  topic := "nonlocal games"
  sources := [
    { paper := BavarianVidickYuen2022, theorem := "Lemma 4.6(1)–(2)",
      locator := "arXiv:1509.07466v2, §4.3, printed pp. 14–15" }
  ]
  theorems := [
    Cslib.PCP.AnchoredDependency.sum_sq_dist_freeTrials_given_wins_le,
    Cslib.PCP.AnchoredDependency.sum_dist_questions_given_wins_le
  ]
  scope := "Finite alphabets and tensor POVMs, with checked answers from the strategy that \
    supplies the positive-probability checked-win event. The first bound sums squared distances \
    and the second sums transcript and question-resampling distances. Distances are half-L1. \
    The constants use natural logs with Pinsker’s factor 1/2 and the full checked-answer \
    alphabet. Any checked set is allowed, including when no free coordinate remains."

register_result "dpll-pigeonhole-refutation-size" where
  title := "The DPLL solver's refutations and certificates of pigeonhole formulas are exponential"
  topic := "SAT algorithms"
  sources := [
    { paper := BeyersdorffGalesiLauria2010, theorem := "Theorem 2",
      locator := "White Rose eprint 74432 (manuscript of 2010-07-01), §4, printed p. 4; PDF p. 5; \
        the bound 2^((n/2) log(n/2 + 1)) at the end of the proof, printed p. 6; PDF p. 7" }
  ]
  theorems := [
    Cslib.Algorithms.Lean.DPLL.pow_half_le_size_refutation?_pigeonhole,
    Cslib.Algorithms.Lean.DPLL.pow_half_le_size_solve_pigeonhole
  ]
  scope := "The source bound holds for every tree-like resolution refutation of PHP^m_n, m > n; \
    these theorems apply it to the output of the library's DPLL solver on PHP^m_n relabelled \
    along any injective numbering Fin m × Fin n → ℕ: the solver finds a refutation with at \
    least (n/2 + 1)^(n/2) nodes and returns an LRAT certificate with at least that many steps \
    (one per leaf of the refutation). The source's proof takes n even; the Lean bound uses \
    floor division n/2 and has no parity hypothesis. Dantchev and Riis (CCC 2001) proved an \
    earlier asymptotic 2^Ω(n log n) bound for regular tree resolution; it is historical \
    context, not a source of this exact bound. These bound the output, not the running time; \
    the running time on the word RAM is issue #6610."

register_result "synchronous-correlations-tracial-representation" where
  title := "Tracial representation of synchronous commuting correlations"
  topic := "nonlocal games"
  sources := [
    { paper := PaulsenEtAl2016, theorem := "Theorem 5.5",
      locator := "arXiv:1407.6918v2, pp. 16–18" }
  ]
  theorems := [
    Cslib.PCP.CommutingStrategy.IsSynchronous.norm_effect_sub_eq_zero,
    Cslib.PCP.CommutingStrategy.IsSynchronous.ofReal_prob_eq_state_alice,
    Cslib.PCP.CommutingStrategy.IsSynchronous.ofReal_prob_eq_state_bob,
    Cslib.PCP.CommutingStrategy.IsSynchronous.prob_comm,
    Cslib.PCP.CommutingStrategy.isSynchronous_swap_iff,
    Cslib.PCP.CommutingStrategy.IsSynchronous.aliceState_isTracial,
    Cslib.PCP.CommutingStrategy.ofTracial_isProjective,
    Cslib.PCP.CommutingStrategy.ofTracial_isSynchronous,
    Cslib.PCP.CommutingStrategy.ofTracial_prob
  ]
  scope := "Pointwise correlations of commuting strategies over complex star-ordered algebras. \
    Zero state distance expresses equality on the GNS vector. The state restricts to a trace on \
    either player's norm-closed generated C*-algebra, exchanging players for Bob. In the converse, \
    a normalized trace and projective measurements give commuting projective actions on its \
    GNS Hilbert space. The complex trace of the product equals the real probability coerced \
    to ℂ. The forward agreement and trace statements allow POVMs."

register_result "synchronous-game-perfect-commuting-equivalence" where
  title := "Perfect commuting strategies and tracial representations of synchronous game algebras"
  topic := "nonlocal games"
  sources := [
    { paper := HeltonEtAl2019, theorem := "Theorem 3.2(3)",
      locator := "published version, pp. 336–338 (game algebra in §3.1)" }
  ]
  theorems := [
    Cslib.PCP.TwoProverGame.exists_isPerfectCommuting_iff,
    Cslib.PCP.TwoProverGame.commutingWinProb_eq_one_iff_isPerfectCommuting
  ]
  scope := "The commuting case of Theorem 3.2. The strategy has zero probability at every \
    rejected tuple. The unital star algebra has projection generators summing to one at each \
    question and zero products at rejected tuples. A faithful tracial representation is obtained \
    on the closed algebra of left GNS operators. The reverse construction uses commuting GNS \
    actions and works with any tracial state. The real-valued score formulation requires full \
    support on question pairs for the implication from score one to pointwise perfection."

register_result "mpda-one-hole-is-no-hole" where
  title := "Complete 1-hole-bounded runs of multistack pushdown automata are well-nested"
  topic := "automata theory"
  sources := [
    { paper := AkshayGastinKrishnaRoychowdhury2020, theorem := "Theorem 2",
      locator := "arXiv:2002.05950v2, Appendix G.1 \"Multi-Producer Consumer\", paragraph \
        \"Hole Bound\", PDF p. 37; holes as in Definition 1, Section 2.1" }
  ]
  theorems := [Cslib.Automata.MPDA.holeBounded_one_iff_wellNested]
  scope := "For every MPDA and every run of its configuration system from a control state with \
    all stacks empty to a control state with all stacks empty, the label sequence of the run is \
    1-hole-bounded exactly when it is well-nested. Open holes are counted through their first \
    pending push that is not closed by a well-nested continuation, consecutive pending pushes \
    of one stack separated by a well-nested factor belonging to the same hole. The paper states \
    the theorem for accepting runs inside its multi-producer consumer example and proves it \
    informally; the Lean statement is for all complete runs and does not need acceptance. \
    Source check: independent agent review (codex-f4a705f4) on PR #6587, against \
    arXiv:2002.05950v2 Definition 1, PDF pp. 5-6, and Appendix G.1, Theorem 2, PDF p. 37."

register_result "quantum-relative-entropy-nonnegative" where
  title := "Nonnegativity of quantum relative entropy for finite density matrices"
  topic := "quantum information"
  sources := [
    { paper := BavarianVidickYuen2022, theorem := "Proposition 5.2",
      locator := "arXiv:1509.07466v2, §5.1, printed p. 19" }
  ]
  theorems := [Cslib.Quantum.relativeEntropy_nonneg]
  scope := "For arbitrary finite complex positive semidefinite trace-one matrices, including \
    singular states, quantum relative entropy is nonnegative. The trace formula uses natural \
    logarithms and requires support containment, stated as reverse kernel inclusion. When that \
    containment fails, the divergence is positive infinity."

register_result "quantum-relative-entropy-joint-convexity" where
  title := "Joint convexity of quantum relative entropy"
  topic := "quantum information"
  sources := [
    { paper := Ruskai2007, theorem := "Theorem 1",
      locator := "arXiv:quant-ph/0604206v1, printed p. 2; proof in §§2.1–2.4" }
  ]
  theorems := [Cslib.Quantum.relativeEntropy_sum_smul_le]
  scope := "Finite complex positive semidefinite matrix pairs with arbitrary nonnegative \
    weights. The normalized weights give joint convexity; this homogeneous form also allows \
    unnormalized weights and assigns positive infinity to a support mismatch. Zero-weight \
    terms contribute zero. The natural-log formula uses the standard positive Umegaki sign \
    as in equation (11), correcting the leading minus sign in the introductory equation (3)."

register_result "classical-quantum-relative-entropy-chain" where
  title := "Relative entropy chain rule for classical–quantum states"
  topic := "quantum information"
  sources := [
    { paper := BavarianVidickYuen2022, theorem := "Proposition 5.6",
      locator := "arXiv:1509.07466v2, §5.1, printed pp. 19–20" }
  ]
  theorems := [Cslib.Quantum.relativeEntropy_classicalQuantumState]
  scope := "For two probability-weighted families of finite-dimensional density matrices, \
    the divergence of the block-diagonal states splits into the classical KL divergence and \
    the source-weighted conditional divergences. The quantum coordinate comes first. Both \
    terms use natural logarithms. Missing support gives positive infinity, and a zero-weight \
    label contributes zero even when its conditional divergence is infinite."

register_result "classical-quantum-mutual-information" where
  title := "Mutual information of a classical–quantum state"
  topic := "quantum information"
  sources := [
    { paper := BavarianVidickYuen2022, theorem := "Proposition 5.7",
      locator := "arXiv:1509.07466v2, §5.1, printed p. 20" }
  ]
  theorems := [Cslib.Quantum.mutualInformation_classicalQuantumState]
  scope := "For finite label distributions and conditional complex density matrices, the \
    mutual information to the product of the actual marginals equals the source-weighted \
    divergence of the conditional states from their quantum marginal. The expression \
    uses natural logarithms and extended divergence with zero contribution at null labels."

register_result "quantum-relative-entropy-partial-trace" where
  title := "Data processing for quantum relative entropy under partial trace"
  topic := "quantum information"
  sources := [
    { paper := BavarianVidickYuen2022, theorem := "Proposition 5.5",
      locator := "arXiv:1509.07466v2, §5.1, printed p. 19" }
  ]
  theorems := [
    Cslib.Quantum.relativeEntropy_partialTraceRight_le,
    Cslib.Quantum.relativeEntropy_partialTraceLeft_le
  ]
  scope := "Either partial trace of two finite complex positive semidefinite matrices has \
    relative entropy bounded by the joint divergence. The theorem extends the trace-one \
    statement to unnormalized matrices, uses natural logarithms and includes singular \
    states. A joint support mismatch makes the right side positive infinity."

register_result "quantum-raz-coordinate-mutual-information" where
  title := "Quantum Raz's coordinate information bound"
  topic := "quantum information"
  sources := [
    { paper := BavarianVidickYuen2022, theorem := "Lemma 5.10",
      locator := "arXiv:1509.07466v2, equation (24), printed p. 21" }
  ]
  theorems := [Cslib.Quantum.sum_mutualInformation_classicalQuantumMarginal_le_relativeEntropy]
  scope := "An arbitrary finite classical tuple, with a possibly different alphabet at each \
    coordinate, and a finite quantum register. The sum of the coordinate mutual informations \
    is bounded by relative entropy to a product classical law with a common density matrix. \
    Natural logarithms, zero-mass labels, singular states and the empty tuple are allowed. \
    Source check by codex-f4a705f4 at \
    https://github.com/cslib-community/cslib-frontier/pull/6660#issuecomment-7020254927."

register_result "classical-quantum-tuple-mutual-information-chain" where
  title := "Mutual information chain rule for finite classical tuples and a quantum register"
  topic := "quantum information"
  sources := [
    { paper := BavarianVidickYuen2022, theorem := "Chain equality in equation (27)",
      locator := "arXiv:1509.07466v2, §5.1, printed p. 21" }
  ]
  theorems := [Cslib.Quantum.mutualInformation_classicalQuantumState_eq_sum_coordinates]
  scope := "Arbitrary finite tuples whose coordinate alphabets may differ, with any joint \
    probability mass function and finite complex density matrices as conditional blocks. \
    The coordinate terms average conditional mutual information over preceding labels, \
    with null prefixes weighted zero. The chain uses natural logarithms and includes the \
    empty tuple."

register_result "quantum-raz-transcript-coordinate-information" where
  title := "Quantum Raz's bound averaged over a classical transcript"
  topic := "quantum information"
  sources := [
    { paper := BavarianVidickYuen2022, theorem := "Claim 5.13 (proof step)",
      locator := "arXiv:1509.07466v2, printed p. 24" }
  ]
  theorems := [Cslib.Quantum.sum_weighted_coordinate_mutualInformation_le_relativeEntropy]
  scope := "For any joint law on a finite transcript and classical tuple with finite complex \
    density blocks, the source-weighted sum of conditional coordinate mutual informations \
    is bounded by the joint relative entropy. The reference may use a different transcript \
    law and specifies independent coordinate laws and a quantum density for each transcript. \
    The theorem uses natural logarithms and includes null labels, singular densities and the \
    empty tuple. The anchored-game instantiation and the full Claim 5.13 remain open. \
    Source check by codex-f4a705f4 at \
    https://github.com/cslib-community/cslib-frontier/pull/6667#issuecomment-7021187449."

register_result "uhlmann-finite-dimensional-local-overlap" where
  title := "Uhlmann’s theorem for finite-dimensional purifications"
  topic := "quantum information"
  sources := [
    { paper := BavarianVidickYuen2022, theorem := "Theorem 5.11",
      locator := "arXiv:1509.07466v2, §5.1, printed p. 22" }
  ]
  theorems := [Cslib.Quantum.exists_localUnitary_inner_eq_rootFidelity]
  scope := "Two complex vectors on the same finite bipartite space, with possibly unequal \
    local dimensions and possibly singular reduced states. A unitary on the right system \
    gives a complex overlap equal to the real unsquared fidelity of the left reductions. \
    Unit vectors recover the normalized purifications in the source."

register_result "powers-stormer-finite-matrices" where
  title := "Powers–Størmer inequality for finite matrices"
  topic := "matrix analysis"
  sources := [
    { paper := SzaboWouters2025, theorem := "Lemma 1.19",
      locator := "published version, §1, printed p. 1397 (tracial norms on p. 1390)" }
  ]
  theorems := [Matrix.trace_sub_mul_self_le_traceNorm_mul_self_sub]
  scope := "For positive semidefinite complex matrices P and Q, the trace of (P − Q)² is \
    bounded by the trace norm of P² − Q². Multiplying the tracial form by the dimension gives \
    ordinary trace, with the empty-dimensional case giving zero on both sides. Singular \
    matrices are allowed, and there is no trace-one assumption."

register_result "fuchs-van-de-graaf-lower" where
  title := "Lower Fuchs–van de Graaf inequality for finite density matrices"
  topic := "quantum information"
  sources := [
    { paper := BavarianVidickYuen2022, theorem := "Lower bound in equation (28)",
      locator := "arXiv:1509.07466v2, §5.1, printed p. 22" }
  ]
  theorems := [Cslib.Quantum.one_sub_rootFidelity_le_traceDistance]
  scope := "Arbitrary finite-dimensional complex positive semidefinite trace-one matrices, \
    including singular states. One minus the unsquared fidelity is bounded above by the \
    trace distance, which is half the trace norm of the difference."

register_result "fuchs-van-de-graaf-upper" where
  title := "Upper Fuchs–van de Graaf inequality for finite density matrices"
  topic := "quantum information"
  sources := [
    { paper := BavarianVidickYuen2022, theorem := "Upper bound in equation (28)",
      locator := "arXiv:1509.07466v2, §5.1, printed p. 22" }
  ]
  theorems := [Cslib.Quantum.traceDistance_le_sqrt_one_sub_rootFidelity_sq]
  scope := "For finite complex positive semidefinite trace-one matrices, including singular \
    states, trace distance is at most the square root of one minus squared root fidelity. \
    Trace distance is half the trace norm of the difference, and root fidelity is unsquared."
