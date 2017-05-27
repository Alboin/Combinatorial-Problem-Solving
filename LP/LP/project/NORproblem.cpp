#include "NORproblem.h"



NORproblem::NORproblem(const int maxDepth, const int nVariables, const vector<bool> truthTableInput)
	:depth(maxDepth), nVars(nVariables), truthTable(truthTableInput)
{
	// Calculate how many nodes are in a tree with maxDepth.
	treeSize = 0;
	for (int i = 0; i <= maxDepth; i++)
		treeSize += pow(2, i);

	// Calculate how many trees are needed to match the number of inputs.
	nDimensions = pow(2, nVariables);

	// Couple the model with the environment.
	model = IloModel(env);

	// Couple all the variables with the environment.
	treeNodes = IloIntVarArray(env);
	treeVariables = IloBoolVarArray(env);
	treeEval = IloBoolVarArray(env);
	treeNOR = IloBoolVarArray(env);
	treeZero = IloBoolVarArray(env);
	
	numberOfNORs = IloExpr(env);


	// Create a vector where the cildren of each node in the tree can be found.
	for (int i = 0; i < treeSize; i++)
		childrenTree.push_back(make_pair((i * 2) + 1, (i * 2) + 2));
	// Create a vector where the parent of each node in the tree can be found.
	for (int i = 0; i < treeSize; i++)
		parentTree.push_back((i-1) / 2);

	// Build the trees with as many nodes and as many dimensions as neccessary.
	for (int i = 0; i < treeSize; i++)
	{
		treeNodes.add(IloIntVar(env, -1, nVariables));
		treeNOR.add(IloBoolVar(env));
		treeZero.add(IloBoolVar(env));
	}
	for (int i = 0; i < treeSize * nDimensions; i++)
	{
		treeEval.add(IloBoolVar(env));
	}
	for (int i = 0; i < treeSize * nVars; i++)
	{
		treeVariables.add(IloBoolVar(env));
	}

	// Fill the vector of possible inputs, where each slot in the vector contains one input combination.
	// The vector contains all possible combinations of inputs.
	for (int count = 0; count < pow(2, nVars); count++)
	{
		vector<bool> tempVec;
		for (int offset = nVars - 1; offset >= 0; offset--)
		{
			int input = ((count & (1 << offset)) >> offset);
			tempVec.push_back(input);
		}
		inputs.push_back(tempVec);
	}

	// Add all the needed constraints.
	addConstraints();
}

NORproblem::~NORproblem()
{
	// Destroy the environment variable.
	env.end();
}

IloIntVar& NORproblem::getNode(const IloIntVarArray &tree, const int dimension, const int node) const
{
	return tree[treeSize * dimension + node];
}

IloBoolVar& NORproblem::getNode(const IloBoolVarArray &tree, const int dimension, const int node) const
{
	return tree[treeSize * dimension + node];
}


IloCplex NORproblem::solveProblem()
{
	cplex = IloCplex(model);

	// Disable logging messages.
	cplex.setOut(env.getNullStream());

	wasSolved = cplex.solve();
	return cplex;
}

void NORproblem::addConstraints()
{
	// The leaf nodes of the tree cannot be NOR-gates.
	for (int i = treeSize / 2; i < treeSize; i++)
	{
		model.add(treeNodes[i] >= 0);
	}

	// The treeNOR and treeZero should match the treeNodes.
	for (int i = 0; i < treeSize; i++)
	{
		model.add(IloIfThen(env, treeNodes[i] == -1, treeNOR[i] == 1));
		model.add(IloIfThen(env, treeNodes[i] != -1, treeNOR[i] == 0));
		model.add(IloIfThen(env, treeNodes[i] == 0, treeZero[i] == 1));
		model.add(IloIfThen(env, treeNodes[i] != 0, treeZero[i] == 0));
	}

	// Count the number of NOR-gates.
	for (int i = 0; i < treeSize; i++)
		numberOfNORs += treeNOR[i];

	// treeVariables should match treeNodes.
	for (int i = 1; i <= nVars; i++)
	{
		for (int j = 0; j < treeSize; j++)
		{
			model.add(IloIfThen(env, treeNodes[j] == i, getNode(treeVariables, i - 1, j) == 1));
			model.add(IloIfThen(env, treeNodes[j] != i, getNode(treeVariables, i - 1, j) == 0));
		}
	}

	// Make sure that the evalTree matches the truthTable.
	for (int i = 0; i < inputs.size(); i++)
	{
		model.add(getNode(treeEval, i, 0) == truthTable[i]);
	}

	//// Make sure that every variableTree-dimension has exactly one variable.
	//for (int i = 0; i < nVars; i++)
	//{
	//	IloExpr temp(env);
	//	for (int j = 0; j < treeSize; j++)
	//	{
	//		temp += getNode(treeVariables, i, j);
	//	}
	//	model.add(temp <= 1);
	//}

	// Make sure that the nodes in evalTree that are inputs are evaluated to their correct values.
	for (int i = 0; i < nVars; i++)
	{
		for (int j = 0; j < treeSize; j++)
		{
			for (int k = 0; k < inputs.size(); k++)
			{
				model.add(IloIfThen(env, getNode(treeVariables, i, j) == 1, getNode(treeEval, k, j) == inputs[k][i]));
			}
		}
	}
	
	// Make sure that the nodes in evalTree that are zeroes are evaluated to 0.
	for (int i = 0; i < treeSize; i++)
	{
		for (int j = 0; j < inputs.size(); j++)
		{
			model.add(IloIfThen(env, treeZero[i] == 1, getNode(treeEval, j, i) == 0));
		}
	}

	// Make sure that the NOR-gates are evaluated correct depending on their children.
	for (int i = 0; i < inputs.size(); i++)
	{
		for (int j = 0; j < treeSize / 2; j++)
		{
			int a = childrenTree[j].first;
			int b = childrenTree[j].second;
			model.add(IloIfThen(env, treeNOR[j] == 1, getNode(treeEval, i, j) == IloMax(0, 1 - getNode(treeEval, i, a) - getNode(treeEval, i, b))));
		}
	}

	// Add the objective function to our model.
	IloObjective objective = IloMinimize(env, numberOfNORs);
	model.add(objective);
}

void NORproblem::print(const IloCplex cplex) const
{
	ofstream output;
	stringstream temp;

	int decimalRepresentation = 0;
	for (int i = 0; i < truthTable.size(); i++)
		decimalRepresentation += truthTable[i] * pow(2, i);

	temp << "output/nlsp_" << depth << "_" << nVars << "_" << decimalRepresentation << ".out";
	string filename;
	temp >> filename;

	output.open(filename);

	output << depth << endl;
	output << nVars << endl;

	cout << endl << endl;
	cout << depth << endl;
	cout << nVars << endl;

	for (int i = 0; i < truthTable.size(); i++)
	{
		output << truthTable[i] << endl;
		cout << truthTable[i] << endl;
	}

	// Print -1 if no solution is found.
	if (!wasSolved)
	{
		cout << -1 << endl;
		output << -1 << endl;
		return;
	}
	// Print the number of NOR-gates and then all the nodes in the tree.
	cout << cplex.getValue(numberOfNORs) << endl;
	output << cplex.getObjValue() << endl;

	for (int i = 0; i < treeSize; i++)
	{
		int num = cplex.getValue(treeNodes[i]);
		cout << i + 1 << " " << num << " ";
		output << i + 1 << " " << num << " ";
		if (cplex.getValue(treeNodes[i]) < 0)
		{
			output << childrenTree[i].first + 1 << " " << childrenTree[i].second + 1 << endl;
			cout << childrenTree[i].first + 1 << " " << childrenTree[i].second + 1 << endl;
		}
		else
		{
			output << "0 0" << endl;
			cout << "0 0" << endl;
		}
	}

	output.close();

}

void NORproblem::debugPrint(const IloCplex cplex, const IloIntVarArray tree, const int dimensions) const
{
	for (int i = 0; i < dimensions; i++)
	{
		for (int j = 0; j < treeSize; j++)
		{
			cout << cplex.getValue(getNode(tree, i, j)) << ", ";
		}
		cout << endl;
	}
	
}

void NORproblem::debugPrint(const IloCplex cplex, const IloBoolVarArray tree, const int dimensions) const
{
	for (int i = 0; i < dimensions; i++)
	{
		for (int j = 0; j < treeSize; j++)
		{
			cout << cplex.getValue(getNode(tree, i, j)) << ", ";
		}
		cout << endl;
	}
}


