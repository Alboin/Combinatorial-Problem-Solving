#include <ilcplex/ilocplex.h>

ILOSTLBEGIN

#include "NORproblem.h"

bool readNORFile(const string &filename, int &maxDepth, int &nInputs, vector<bool> &truthTable);

int main(int argc, char *argv[])
{
	string filename;

	for (int i = 1; i < argc; i++)
	{
		// argv[i] is the argument at index i
		filename.append(argv[i]);
	}

	//filename = "instances/nlsp_2_2_8.inp";
	//filename = "instances/nlsp_1_3_236.inp";
	string location = "instances/";
	//cin >> filename;
	location.append(filename); //TODO: use this instead of filename.
	
	vector<bool> truthTable;
	int maxDepth, nInputs;

	// Read an input-file and fill the neccesary values needed for the NOR-problem.
	bool readSuccessful = readNORFile(location, maxDepth, nInputs, truthTable);
	
	if (readSuccessful)
	{
		// Create the NOR-problem
		NORproblem solvethisplease(maxDepth, nInputs, truthTable);

		// Try to solve the problem and print the result.
		IloCplex possibleSolution = solvethisplease.solveProblem();
		solvethisplease.print(possibleSolution);
	}

	return 0;
}

bool readNORFile(const string &filename, int &maxDepth, int &nInputs, vector<bool> &truthTable)
{
	ifstream inputFile;
	inputFile.open(filename);

	if (!inputFile)
	{
		cout << "File '" << filename << "' could not be opened." << endl << endl;
		return false;
	}

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

	// Get the nlsp-information from the file.
	ss >> maxDepth;
	ss >> nInputs;

	int truthTableEntry;
	while (ss >> truthTableEntry)
		truthTable.push_back(truthTableEntry);

	return true;
}