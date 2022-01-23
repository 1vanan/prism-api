package demos;

import parser.State;
import parser.ast.DeclarationInt;
import parser.ast.DeclarationBool;
import parser.ast.DeclarationArray;
import parser.ast.DeclarationType;
import parser.ast.Expression;
import parser.type.Type;
import parser.type.TypeInt;
import parser.type.TypeBool;
import parser.type.TypeArray;
import prism.ModelGenerator;
import prism.ModelType;
import prism.Prism;
import prism.PrismDevNullLog;
import prism.PrismException;
import prism.PrismLog;
import prism.RewardGenerator;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class DTMCCNFChecker {
    public static void main(String[] args) {
        new DTMCCNFChecker().run();
    }

    public void run() {
        try {
            // Create a log for PRISM output (hidden or stdout)
            PrismLog mainLog = new PrismDevNullLog();
            //PrismLog mainLog = new PrismFileLog("stdout");

            // Initialise PRISM engine
            Prism prism = new Prism(mainLog);
            prism.initialise();

            // Create a list of arrays, each of which defines a literal from CNF specification.
            // For example, 3 organizations, and CNF: (o1 & o2) || (o2 & o3). Then arrays will be:
            // [1, 1, 0]; [0, 1, 1]
            List<int[]> spec = new ArrayList<>();
            spec.add(new int[]{1, 1});

            // List of probabilities for each organization. Goes in the same order
            List<Double> probabilities = Arrays.asList(0.5, 0.5);

            // Create a model generator to specify the model that PRISM should build
            CNFCheck modelGen = new CNFCheck(2, probabilities, spec);

            // Load the model generator into PRISM,
            // export the model to a dot file (which triggers its construction)
            prism.loadModelGenerator(modelGen);
            prism.exportTransToFile(true, Prism.EXPORT_DOT_STATES, new File("dtmc.dot"));

            // Then do some model checking and print the result
            String[] props = new String[]{
                    "P=?[F \"end\"]"
            };
            for (String prop : props) {
                System.out.println(prop + ":");
                System.out.println(prism.modelCheck(prop).getResult());
            }

            // Close down PRISM
            prism.closeDown();

        } catch (FileNotFoundException e) {
            System.out.println("Error: " + e.getMessage());
            System.exit(1);
        } catch (PrismException e) {
            System.out.println("Error: " + e.getMessage());
            System.exit(1);
        }
    }

    /**
     * ModelGenerator defining a discrete-time Markov chain (DTMC) model
     * of a consensus model for n organizations. List of arrays define specification for the consensus model:
     * each array is a literal, where 1 - organization shall give a confirmation reply.
     */
    class CNFCheck implements ModelGenerator, RewardGenerator {
        // Size of the tree (state x is in [0,...,n])
        private int n;
        List<Double> probabilities;
        // Current state being explored
        private State exploreState;
        // Current value of x
        private int x;
        // replied of organizations. 1 - confirmation, 0 - refusal
        public int testArr[];
        List<int[]> scpec;

        /**
         * Construct a new model generator
         *
         * @param n Number of organizations
         * @param probabilities Probability of each organization to give a confirmation response
         * @param scpec List of arrays, where each array represents a literal from the CNF
         */
        public CNFCheck(int n, List<Double> probabilities, List<int[]> scpec) {
            this.n = n;
            this.probabilities = probabilities;
            this.scpec = scpec;

            testArr = new int[n];
        }

        // Methods for ModelInfo interface

        // The model is a discrete-time Markov chain (DTMC)

        @Override
        public ModelType getModelType() {
            return ModelType.DTMC;
        }

        @Override
        public List<String> getVarNames() {
            List<String> varNames = new ArrayList<>();
            varNames.add("x");
            for (int i = 0; i < n; i++) {
                varNames.add("o" + i);
            }
            return varNames;
        }

        @Override
        public List<Type> getVarTypes() {
            return Arrays.asList(TypeInt.getInstance());
        }

        @Override
        public DeclarationType getVarDeclarationType(int i) {
            return new DeclarationInt(Expression.Int(0), Expression.Int(n));

        }

        @Override
        public List<String> getLabelNames() {
            return Arrays.asList("end");
        }

        // Methods for ModelGenerator interface (rather than superclass ModelInfo)

        @Override
        public State getInitialState() throws PrismException {
            State initialState = new State(3);

            for (int i = 0; i <= n; i++) {
                initialState.setValue(i, 0);
            }

            return initialState;
        }

        @Override
        public void exploreState(State exploreState) throws PrismException {
            // Store the state (for reference, and because will clone/copy it later)
            this.exploreState = exploreState;
            // Cache the value of x in this state for convenience
            x = (Integer) exploreState.varValues[0];

            for (int i = 0; i < n; i++) {
                testArr[i] = (Integer) exploreState.varValues[i + 1];
            }
        }

        @Override
        public int getNumChoices() throws PrismException {
            // This is a DTMC so always exactly one nondeterministic choice (i.e. no nondeterminism)
            return 1;
        }

        @Override
        public int getNumTransitions(int i) throws PrismException {
            // End points have a self-loop, all other states have 2 transitions, left and right
            // (Note that i will always be 0 since this is a Markov chain)
            return (x == n) ? 1 : 2;
        }

        @Override
        public Object getTransitionAction(int i, int offset) throws PrismException {
            // No action labels in this model
            return null;
        }

        @Override
        public double getTransitionProbability(int i, int offset) throws PrismException {
            // End points have a self-loop (with probability 1)
            // All other states go left with probability 1-p and right with probability p
            // We assume that these are transitions 0 and 1, respectively
            // (Note that i will always be 0 since this is a Markov chain)

            if (x < n) {
                return offset == 0 ? 1 - probabilities.get(x) : probabilities.get(x);
            } else return 1;
        }

        @Override
        public State computeTransitionTarget(int i, int offset) throws PrismException {
            // End points have a self-loop (with probability 1)
            // All other states go left with probability 1-p and right with probability p
            // We assume that these are transitions 0 and 1, respectively
            // (Note that i will always be 0 since this is a Markov chain)
            State target = new State(exploreState);
            if (x == n) {
                // Self-loop
                return target;
            } else {
                return target.setValue(0, x + 1).setValue(x + 1, offset == 0 ? 0 : 1);
            }
        }

        @Override
        public boolean isLabelTrue(int i) throws PrismException {
            boolean containsOne = false;

            for (int[] ints : scpec) {
                if (Arrays.equals(ints, testArr)) {
                    containsOne = true;
                    break;
                }
            }

            // If we traversed the whole tree and went through the path of the confirmation, then there is a desired state
            return (x == n && containsOne);
        }

        // Methods for RewardGenerator interface (reward info stored separately from ModelInfo/ModelGenerator)

        // There is a single reward structure, r, which just assigns reward 1 to every state.
        // We can use this to reason about the expected number of steps that occur through the random walk.

        @Override
        public List<String> getRewardStructNames() {
            return Arrays.asList("r");
        }

        @Override
        public double getStateReward(int r, State state) throws PrismException {
            // r will only ever be 0 (because there is one reward structure)
            // We assume it assigns 1 to all states.
            return 1.0;
        }

        @Override
        public double getStateActionReward(int r, State state, Object action) throws PrismException {
            // No action rewards
            return 0.0;
        }
    }

    class ConsensusState {
        int stepsNum = 0;

        List<String> acceptanceResponses = new ArrayList<>();
    }
}
