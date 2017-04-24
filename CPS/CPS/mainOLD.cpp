#include <gecode/int.hh>
#include <gecode/minimodel.hh>	
#include <gecode/search.hh>


using namespace Gecode;
using namespace std;

class QueenProblem : public Space {
protected:
	IntVarArray board;
	int nQueens;
public:
	QueenProblem(int n)
		: board(*this, n*n, 0, 1), nQueens(n)
	{
		// Make sure there is only nQueens in total.
		linear(*this, board, IRT_EQ, nQueens);

		// Make sure there is only one queen per row.
		for (int i = 0; i < nQueens; i++)
		{
			IntVarArgs row(nQueens);
			for (int j = 0; j < nQueens; j++)
				row[j] = board[i*nQueens + j];
			linear(*this, row, IRT_EQ, 1);
		}

		// Make sure there is only one queen per column.
		for (int i = 0; i < nQueens; i++)
		{
			IntVarArgs column(nQueens);
			for (int j = 0; j < nQueens; j++)
				column[j] = board[i + j * nQueens];
			linear(*this, column, IRT_EQ, 1);
		}

		// Make sure there is no queen diagonal to another
		for (int i = 0; i < nQueens; i++)
		{
			for (int j = 0; j < nQueens; j++)
			{
				int d = i - j;


			}
		}

		// Tell Gecode how to perform the search.
		branch(*this, board, INT_VAR_NONE(), INT_VAL_MAX());

	}
	// Compy constructor required for Gecode search-algorithm
	QueenProblem(bool share, QueenProblem& q)
		: Space(share, q), nQueens(q.nQueens)
	{
		board.update(*this, share, q.board);
	}
	virtual Space* copy(bool share)
	{
		return new QueenProblem(share, *this);
	}

	void print()
	{
		for (int i = 0; i < nQueens * nQueens; i++)
		{
			if (i % nQueens == 0)
				cout << endl;
			cout << (board[i].val() ? "X" : ".") << " ";
		}
		cout << endl;
	}
};

int mainOLD()
{
	try {
		QueenProblem *q = new QueenProblem(4);

		DFS<QueenProblem> d(q);
		delete q;

		while (QueenProblem *temp = d.next())
		{
			temp->print();
			delete temp;
		}
	}
	catch (Exception e)
	{
		cerr << "Gecode: " << e.what() << endl;
		return 1;
	}


	char dummy;
	cin >> dummy;

	return 0;
}