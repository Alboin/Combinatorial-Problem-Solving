#include <gecode/int.hh>
#include <gecode/minimodel.hh>	
#include <gecode/search.hh>
#include <chrono>
#include <iostream>
#include <fstream>
#include <ostream>
#include <sstream>

using namespace Gecode;
using namespace std;
using namespace std::chrono;

high_resolution_clock::time_point start_time;

class NORproblem : public Space {
protected:

	IntVarArray treeNodes;
	BoolVarArray treeEval;
	BoolVarArray treeEvalHelper;

	BoolVarArray treeNOR;
	BoolVarArray treeZero;

	BoolVarArray inputMatch;

	vector<pair<int,int> > referenceTree;
	vector<vector<int> > allPossibleInputs;
	vector<int> truthTable;

	IntVar size;
	
	int maxDepth;
	int numberOfInputs;
	int treeSize = 0;


public:

	NORproblem(int depth, int inputs, vector<int> truth)
		:maxDepth(depth), numberOfInputs(inputs), truthTable(truth)
	{
		#pragma region Initiation of variables and constants.
		// Create an array representing a tree where each node can be input, 0 or NOR.
		for (int i = 0; i <= maxDepth; i++)
			treeSize += pow(2, i);

		treeNodes = IntVarArray(*this, treeSize, -1, numberOfInputs);
		treeEval = BoolVarArray(*this, treeSize * truthTable.size(), 0, 1);
		treeEvalHelper = BoolVarArray(*this, treeSize * truthTable.size(), 0, 1);
		
		// Two boolean trees for whether a node is NOR or zero.
		treeNOR = BoolVarArray(*this, treeSize, 0, 1);
		treeZero = BoolVarArray(*this, treeSize, 0, 1);

		// A boolean tree for each input variable.
		inputMatch = BoolVarArray(*this, treeSize * numberOfInputs, 0, 1);

		// A int for counting the number of NOR-gates in the tree.
		size = IntVar(*this, 0, treeSize);
		
		// Create an array where the cildren of each node in the tree can be found.
		for (int i = 0; i < treeSize; i++)
			referenceTree.push_back(make_pair((i*2) + 1, (i*2) + 2));


		// Create a 2-dimensional vector where the second dimension is the input variables and
		// the first is one combination of values for those inputs.
		// This vector contains all possible combinations of inputs.
		for (int count = 0; count < pow(2, numberOfInputs); count++)
		{
			vector<int> tempVec;
			for (int offset = numberOfInputs - 1; offset >= 0; offset--)
			{
				int input = ((count & (1 << offset)) >> offset);
				tempVec.push_back(input);
			}
			allPossibleInputs.push_back(tempVec);
		}
		#pragma endregion

		// Constraint: Make sure that the size-variable has the correct size.
		linear(*this, treeNOR, IRT_EQ, size);

		// Constraint: Make sure that the treeEval and treeEvalHelper matches.
		/*for (int node = 0; node < treeSize; node++)
		{
			for (int truthNumber = 0; truthNumber < truthTable.size(); truthNumber++)
			{
				rel(*this, evaluate(node, truthNumber), IRT_NQ, inverseEvaluate(node, truthNumber));
			}
		}*/

		// Loop through the whole tree and apply constraints depending on what kind of node the current one is.
		for (int node = 0; node < treeSize; node++)
		{
			#pragma region CONSTRAINTS FOR NODES = -1
			// Constraint: If the node is a NOR-gate, mark that node as "true" in the treeNOR.
			rel(*this, treeNodes[node], IRT_EQ, -1, treeNOR[node]);

			// If the node is a leaf.
			if (node >= treeSize / 2)
			{
				// Constraints: If the node is a leaf it cannot be a NOR-gate.
				rel(*this, treeNodes[node], IRT_NQ, -1);
				//rel(*this, treeNOR[node], IRT_EQ, 0); - should not be needed
			}

			int left = referenceTree[node].first, right = referenceTree[node].second;
			for (int j = 0; j < truthTable.size(); j++)
			{
				// If the node is not a leaf.
				if (node < treeSize / 2)
				{
					// Constraint: The inverseEvaluate works like on OR. If either of the two children left & right are true so are the parent.
					rel(*this, inverseEvaluate(right, j), BOT_OR, inverseEvaluate(left, j), inverseEvaluate(node, j));
					// Constraint: Then since "evaluate == !inverseEvaluate" we get a NOR.
					//rel(*this, evaluate(node, j), IRT_NQ, inverseEvaluate(node, j), imp(treeNOR[node]));
				}
			}
			#pragma endregion

			#pragma region CONSTRAINTS FOR NODES = 0
			// Constraint: If the node is a 0, mark that node as "true" in the treeZero.
			rel(*this, treeNodes[node], IRT_EQ, 0, treeZero[node]);
			// Constraint: If the node is a 0, make sure it evaluates to 0.
			for (int j = 0; j < truthTable.size(); j++)
				rel(*this, inverseEvaluate(node, j), IRT_EQ, 1, imp(treeZero[node]));
				//rel(*this, evaluate(node, j), IRT_EQ, 0, imp(treeZero[node]));
			#pragma endregion

			#pragma region CONSTRAINTS FOR NODES = 1, 2, 3...
			// Constraint: Make sure that the tree inputMatch get the correct values through the function "isInput()".
			for (int input = 1; input <= numberOfInputs; input++)
			{
				rel(*this, treeNodes[node], IRT_EQ, input, isInput(node, input));
			}

			for (int truthTableEntry = 0; truthTableEntry < truthTable.size(); truthTableEntry++)
			{
				for (int input = 1; input <= numberOfInputs; input++)
				{
					bool inputEval = allPossibleInputs[truthTableEntry][input - 1];
					// Constraint: Make sure that the treeEval gets the correct value from the input-node.
					//rel(*this, evaluate(node, truthTableEntry), IRT_EQ, inputEval, imp(isInput(node, input)));
					rel(*this, inverseEvaluate(node, truthTableEntry), IRT_NQ, inputEval, imp(isInput(node, input)));
				}
			}

			#pragma endregion
		}
		
		// Constraint: Make sure that the output matches the truth-table.
		for (int i = 0; i < truthTable.size(); i++)
		{
			rel(*this, inverseEvaluate(0, i), IRT_NQ, truthTable[i]);
			//rel(*this, treeEval[i * treeSize], IRT_EQ, truthTable[i]);
			//rel(*this, evaluate(0, i), IRT_EQ, truthTable[i]);
		}

		// Constraint: Make sure the tree has not more or less inputs than requested.
		linear(*this, inputMatch, IRT_EQ, numberOfInputs);
		// Constraint: Make sure there is only one appearance of one input.
		for (int input = 1; input <= numberOfInputs; input++)
		{
			BoolVarArgs oneInput(treeSize);
			for (int node = 0; node < treeSize; node++)
			{
				oneInput[node] = isInput(node, input);
			}
			linear(*this, oneInput, IRT_EQ, 1);
		}

		// TODO: MINIMIZE THE SIZE (NUMBER OF NOR-GATES)
		// Tell Gecode how to perform the search.
		branch(*this, treeNodes, INT_VAR_NONE(), INT_VAL_MIN());
	}

	/*BoolVar evaluate(int node, int truthNumber)
	{
		//treeSize * truthTable
		return treeEval[truthNumber * treeSize + node];
	}*/

	BoolVar inverseEvaluate(int node, int truthNumber)
	{
		//treeSize * truthTable
		return treeEvalHelper[truthNumber * treeSize + node];
	}

	BoolVar isInput(int node, int input)
	{
		//treeSize * numberOFInputs
		//since the variable "input" will be 1, 2, 3...etc we need to subtract 1 to get the correct index.
		return inputMatch[(input-1) * treeSize + node];
	}
	
	// Copy constructor required for Gecode search-algorithm
	NORproblem(bool share, NORproblem& nor)
		: Space(share, nor), maxDepth(nor.maxDepth), numberOfInputs(nor.numberOfInputs), treeSize(nor.treeSize),
		referenceTree(nor.referenceTree), allPossibleInputs(nor.allPossibleInputs), truthTable(nor.truthTable)
	{
		//Abort program if a search is performed during more than 100 seconds.
		auto duration = duration_cast<microseconds>(high_resolution_clock::now() - start_time).count();
		float durationInSeconds = duration / 1000000.0;

		treeNodes.update(*this, share, nor.treeNodes);
		treeEval.update(*this, share, nor.treeEval);
		treeEvalHelper.update(*this, share, nor.treeEvalHelper);

		treeNOR.update(*this, share, nor.treeNOR);
		treeZero.update(*this, share, nor.treeZero);

		inputMatch.update(*this, share, nor.inputMatch);

		size.update(*this, share, nor.size);

		cout << endl << "copying!" << durationInSeconds;
	}

	virtual Space* copy(bool share)
	{
		return new NORproblem(share, *this);
	}

	virtual void constrain(const Space& _m)
	{
		const NORproblem& m = static_cast<const NORproblem&>(_m);

		rel(*this, size, IRT_LQ, m.size);
	}

	void print(bool succeeded)
	{
		ofstream output;
		stringstream temp;

		int decimalRepresentation = 0;
		for (int i = 0; i < truthTable.size(); i++)
			decimalRepresentation += truthTable[i] * pow(2, i);

		temp << "nlsp_" << maxDepth << "_" << numberOfInputs << "_" << decimalRepresentation << ".out";
		string filename;
		temp >> filename;

		output.open(filename);
		
		output << maxDepth << endl;
		output << numberOfInputs << endl;

		cout << endl << endl;
		cout << maxDepth << endl;
		cout << numberOfInputs << endl;

		for (int i = 0; i < truthTable.size(); i++)
		{
			output << truthTable[i] << endl;
			cout << truthTable[i] << endl;
		}

		/*cout << "Evaluation: ";
		for (int i = 0; i < truthTable.size(); i++)
			cout << evaluate(0, i).val() << " ";
		cout << endl;
		*/
		// Print -1 if no solution is found.
		if (!succeeded)
		{
			cout << -1 << endl;
			output << -1 << endl;
			return;
		}
		// Print the number of NOR-gates and then all the nodes in the tree.
		cout << size.val() << endl;
		output << size.val() << endl;

		for (int i = 0; i < treeSize; i++)
		{
			cout << i + 1 << " " << treeNodes[i].val() << " ";
			output << i + 1 << " " << treeNodes[i].val() << " ";
			if (treeNodes[i].val() < 0)
			{
				output << referenceTree[i].first + 1 << " " << referenceTree[i].second + 1 << endl;
				cout << referenceTree[i].first + 1 << " " << referenceTree[i].second + 1 << endl;
			}
			else
			{
				output << "0 0" << endl;
				cout << "0 0" << endl;
			}
		}

		/*for (int node = 0; node < treeSize; node++)
		{
			for (int i = 0; i < truthTable.size(); i++)
			{
				cout << evaluate(node, i).val() << " ";
			}
			cout << endl;
		}*/




		output.close();

	}
};



int main()
{
	// Read an input-file.
	cout << "Enter input filename: ";

	string filename;
	//cin >> filename;
	filename = "nlsp_2_2_8.inp"; // used during debugging
	cout << filename;

	ifstream inputFile;
	inputFile.open(filename);
	stringstream ss;

	string line;
	if (inputFile.is_open())
	{
		while (getline(inputFile, line))
		{
			ss << line;
			ss << " ";
		}
		inputFile.close();
	}
	
	int maxDepth, nInputs;
	ss >> maxDepth;
	ss >> nInputs;

	int truthTableEntry;
	vector<int> truthTable;
	while (ss >> truthTableEntry)
		truthTable.push_back(truthTableEntry);

	// Create a NORproblem from the input-file info and solve it.
	try {

		NORproblem *nor = new NORproblem(maxDepth, nInputs, truthTable);

		start_time = high_resolution_clock::now();
		Gecode::Search::Stop::time(5000);

		BAB<NORproblem> d(nor);

		// If no solution is found.
		if (!d.next())
			nor->print(false);
		delete nor;

		while (NORproblem *temp = d.next())
		{
			temp->print(true);
			char dummy;
			cin >> dummy;
			delete temp;
		}
	}
	catch (Exception e)
	{
		cerr << endl << "Gecode: " << e.what() << endl;
		char dummy;
		cin >> dummy;
		return 1;
	}
		
	char dummy;
	cin >> dummy;

	return 0;
}