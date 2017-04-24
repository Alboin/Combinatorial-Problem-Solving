#include <gecode/int.hh>
#include <gecode/minimodel.hh>	
#include <gecode/search.hh>
//#include <chrono>
#include <iostream>
#include <fstream>
#include <ostream>
#include <sstream>

using namespace Gecode;
using namespace std;
//using namespace std::chrono;

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
	
	int maxDepth;
	int numberOfInputs;
	int treeSize = 0;


public:

	NORproblem(int depth, int inputs, vector<int> truth)
		:maxDepth(depth), numberOfInputs(inputs), truthTable(truth)
	{
		// Create an array representing a tree where each node can be input, 0 or NOR.
		int nodeSize = 4;

		for (int i = 0; i <= maxDepth; i++)
			treeSize += pow(2, i);

		cout << endl << "treeSize: " << treeSize << " truthTable.size(): " << truthTable.size() << " numberOfInputs: " << numberOfInputs << endl;
		// Debug printing
		//cout << endl << maxDepth << endl;
		//cout << numberOfInputs << endl;
		//for (int i = 0; i < truthTable.size(); i++)
			//cout << truthTable[i] << endl;

		treeNodes = IntVarArray(*this, treeSize, -1, treeSize);
		treeEval = BoolVarArray(*this, treeSize * truthTable.size(), 0, 1);
		treeEvalHelper = BoolVarArray(*this, treeSize * truthTable.size(), 0, 1);
		
		// Two boolean trees for whether a node is NOR or zero.
		treeNOR = BoolVarArray(*this, treeSize, 0, 1);
		treeZero = BoolVarArray(*this, treeSize, 0, 1);

		// A boolean tree for each input variable.
		inputMatch = BoolVarArray(*this, treeSize * numberOfInputs, 0, 1);
		
		// Create an array where the cildren of each node in the tree can be found.
		for (int i = 0; i < treeSize; i++)
			referenceTree.push_back(make_pair((i*2) + 1, (i*2) + 2));

		cout << "hit1" << endl;

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

		cout << "hit2" << endl;

		// Make sure that the two boolean trees has the correct values.
		for (int i = 0; i < treeNodes.size(); i++)
		{
			rel(*this, treeNodes[i], IRT_EQ, -1, treeNOR[i]);
			rel(*this, treeNodes[i], IRT_EQ, 0, treeZero[i]);
		}

		cout << "hit3" << endl;

		// LOOPS THROUGH THE TREE
		for (int i = 0; i < treeSize; i++)
		{
			// i = current node

			int left = referenceTree[i].first, right = referenceTree[i].second;
			// left & right replaces i when used.

			// LOOPS THROUGH EVAL-TREES
			for (int j = 0; j < treeSize * truthTable.size(); j += treeSize)
			{
				// j = current eval-tree.
				// j + i = current node in current eval-tree.

				// If the node is not a leaf.
				if (i < treeSize / 2)
				{
					// If the node is a NOR-gate.
					rel(*this, treeNodes[i], IRT_EQ, -1, treeNOR[i]);
					// The treeEvalHelper works like on OR.
					rel(*this, treeEval[right + j], BOT_OR, treeEval[left + j], treeEvalHelper[i + j]);
					// Then since "treeEval == !treeEvalHelper" we get a NOR.
					rel(*this, treeEval[i + j], IRT_NQ, treeEvalHelper[i + j], imp(treeNOR[i]));
				}
				// If the node is a leaf.
				else
				{
					// If the node is a leaf it cannot be a NOR-gate.
					rel(*this, treeNodes[i], IRT_NQ, -1);
					rel(*this, treeNOR[i], IRT_EQ, 0);
				}

				// If the node is a 0.
				rel(*this, treeNodes[i], IRT_EQ, 0, treeZero[i]);
				rel(*this, treeEval[j + i], IRT_EQ, 0, imp(treeZero[i]));

				// LOOPS THROUGH THE DIFFERENT INPUT-COMBINATIONS
				for (int nInputCombination = 0; nInputCombination < allPossibleInputs.size(); nInputCombination++)
				{
					// k = current inputMatch-tree
					// k + i = current node in current inputMatch-tree.

					// LOOPS THROUGH THE SELECTED INPUT-COMBINATION
					for (int input = 0; input < numberOfInputs; input++)
					{
						bool inputEval = allPossibleInputs[nInputCombination][input];

						// Making inputMatch true if the tree-node has the same id as the input.
						rel(*this, treeNodes[i], IRT_EQ, input + 1, inputMatch[(input*treeSize) + i]);
						
						// Evaluating the nodes value to the input, if the previous constraint is true.
						rel(*this, treeEval[j + i], IRT_EQ, inputEval, imp(inputMatch[(input*treeSize) + i]));

					}
				}
			}
		}


		// Make sure that the tree evaluates correct.
		// Loop through all nodes in the tree.
		/*for (int i = 0; i < treeSize; i++)
		{
			int left = referenceTree[i].first, right = referenceTree[i].second;
			// Loop through all input combinations.
			for (int j = 0; j < treeEval.size() - i; j += treeSize)
			{
				cout << "hit31";

				// If the node is not a leaf.
				if (i <= treeSize / 2)
				{
					// If the node is a NOR-gate.
					rel(*this, treeNodes[i], IRT_EQ, -1, treeNOR[i]);
					// The treeEvalHelper works like on OR.
					rel(*this, treeEval[j + right], BOT_OR, treeEval[j + left], treeEvalHelper[i + j]);
					// Then since "treeEval == !treeEvalHelper" we get a NOR.
					rel(*this, treeEval[i + j], IRT_NQ, treeEvalHelper[i + j], imp(treeNOR[i]));
				}
				// If the node is a leaf.
				else
				{
					// If the node is a leaf it cannot be a NOR-gate.
					rel(*this, treeNodes[i], IRT_NQ, -1);
				}


				
				
				cout << "hit32";
				
				// If the node is an input.
				// For selected node, loop through all inputs in selected input combination.
				for (int nInputCombination = 0; nInputCombination < allPossibleInputs.size(); nInputCombination++)
				{
					for (int k = 0; k < numberOfInputs; k++)
					{
						cout << "1";
						bool inputEval = allPossibleInputs[nInputCombination][k];
						// Making inputMatch true if the tree-node has the same id as the input.
						cout << "2";
						rel(*this, treeNodes[i], IRT_EQ, k + 1, inputMatch[(k*treeSize) + i]);
						cout << "3";
						// Evaluating the nodes value to the input, if the previous constraint is true.
						rel(*this, treeEval[j + i], IRT_EQ, inputEval, imp(inputMatch[(i*treeSize) + k]));
						cout << "4";

					}
				}
				cout << "hit33";

				// If the node is a 0.
				rel(*this, treeNodes[i], IRT_EQ, 0, treeZero[i]);
				rel(*this, treeEval[j + i], IRT_EQ, 0, imp(treeZero[i]));
				
			}
		}*/
		
		cout << "hit4" << endl;
		// Make sure that the output matches the truth-table.
		for (int i = 0; i < truthTable.size(); i++)
		{
			rel(*this, treeEval[i * treeSize], IRT_EQ, truthTable[i]);
		}
		cout << "hit5";
		//TODO
		// Measure the tree-size.

		// Make sure the tree has not more or less inputs than requested.
		/*BoolVarArgs nonInputs(treeSize * 2);
		for (int i = 0; i < treeSize * 2; i++)
		{
			nonInputs[(i*2)] = treeNOR[i];
			nonInputs[(i*2)+1] = treeZero[i];
		}
		linear(*this, nonInputs, IRT_EQ, treeSize - numberOfInputs);
		*/
		//TODO
		// Add branches for all the variables neccessary.

		// TODO: MINIMIZE THE SIZE (NUMBER OF NOR-GATES)
		// Tell Gecode how to perform the search.
		branch(*this, treeNodes, INT_VAR_NONE(), INT_VAL_MIN());
		/*branch(*this, treeEval, INT_VAR_NONE(), INT_VAL_MIN());
		branch(*this, treeEvalHelper, INT_VAR_NONE(), INT_VAL_MIN());
		branch(*this, treeNOR, INT_VAR_NONE(), INT_VAL_MIN());
		branch(*this, treeZero, INT_VAR_NONE(), INT_VAL_MIN());
		branch(*this, inputMatch, INT_VAR_NONE(), INT_VAL_MIN());*/
	}
	
	// Copy constructor required for Gecode search-algorithm
	NORproblem(bool share, NORproblem& nor)
		: Space(share, nor), maxDepth(nor.maxDepth), numberOfInputs(nor.numberOfInputs), treeSize(nor.treeSize),
		referenceTree(nor.referenceTree), allPossibleInputs(nor.allPossibleInputs), truthTable(nor.truthTable)
	{
		treeNodes.update(*this, share, nor.treeNodes);
		treeEval.update(*this, share, nor.treeEval);
		treeEvalHelper.update(*this, share, nor.treeEvalHelper);

		treeNOR.update(*this, share, nor.treeNOR);
		treeZero.update(*this, share, nor.treeZero);

		inputMatch.update(*this, share, nor.inputMatch);

		cout << endl << "copying! treesize: " << treeSize;
		//cout << treeEval.size() << endl;
		//cout << treeNOR.size() << endl;
		//cout << treeNodes.size() << endl;
	}

	virtual Space* copy(bool share)
	{
		return new NORproblem(share, *this);
	}

	void print()
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

		for (int i = 0; i < truthTable.size(); i++)
		{
			output << truthTable[i] << endl;
		}

		//print number of nor-gates here, or -1 if failed.
		for (int i = 0; i < treeSize; i++)
		{
			output << i + 1 << " " << treeNodes[i].val() << " ";
			if (treeNodes[i].val() > 0)
				output << referenceTree[i].first << " " << referenceTree[i].second << endl;
			else
				output << "0 0" << endl;
		}
		output << "treeSize: " << treeSize;

		output.close();
		cout << "hejja";

	}
};



int main()
{
	// TODO: Where should I put these?
	//high_resolution_clock::time_point start_time = high_resolution_clock::now();
	//auto duration = duration_cast<microseconds>(high_resolution_clock::now() - start_time).count();
	//float durationInSeconds = duration / 1000000.0;
	
	//Testing
	int numberOfInputs = 3;
	vector<vector< int> > allPossibleInputs;

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

	for (int i = 0; i < allPossibleInputs.size(); i++)
	{
		for (int j = 0; j < numberOfInputs; j++)
		{
			cout << allPossibleInputs[i][j];
		}
		cout << endl;
	}
	//end of testing

	
	// Read an input-file.
	cout << "Enter input filename: ";

	string filename;
	//cin >> filename;
	filename = "nlsp_2_2_6.inp"; // used during debugging

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

		DFS<NORproblem> d(nor);
		delete nor;

		while (NORproblem *temp = d.next())
		{
			temp->print();
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