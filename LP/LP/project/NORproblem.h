#pragma once

#include <ilcplex/ilocplex.h>
#include <ilconcert\iloalg.h>

ILOSTLBEGIN

#include <vector>

using namespace std;

class NORproblem
{
public:
	NORproblem(const int maxDepth, const int nVariables, const vector<bool> truthTableInput);
	~NORproblem();

	IloCplex solveProblem();
	void print(const IloCplex cplex) const;
	void debugPrint(const IloCplex cplex, const IloIntVarArray tree, const int dimensions) const;
	void debugPrint(const IloCplex cplex, const IloBoolVarArray tree, const int dimensions) const;
private:

	const int depth;
	const int nVars;
	const vector<bool> truthTable;
	vector<vector<bool>> inputs;
	vector<pair<int, int>> childrenTree;
	vector<int> parentTree;

	int treeSize;
	int nDimensions;
	bool wasSolved = false;

	// Create the cplex environment.
	IloEnv env;
	// Create the cplex model.
	IloModel model;
	// Create the cplex solver, used in function "solveProblem()".
	IloCplex cplex;

	// A variable that keeps count on the number of NOR-gates used.
	IloExpr numberOfNORs;

	// Integer trees
	IloIntVarArray treeNodes;
	// Boolean trees
	IloBoolVarArray treeEval;
	IloBoolVarArray treeNOR;
	IloBoolVarArray treeZero;
	IloBoolVarArray treeVariables;

	void addConstraints();
	IloBoolVar& getNode(const IloBoolVarArray &tree, const int dimension, const int node) const;
	IloIntVar& getNode(const IloIntVarArray &tree, const int dimension, const int node) const;

};

