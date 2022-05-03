#include <bits/stdc++.h>
#include <lemon/list_graph.h>
#include <lemon/lgf_reader.h>
#include <lemon/lgf_writer.h>
#include <lemon/graph_to_eps.h>
#include <lemon/time_measure.h>
#include <lemon/arg_parser.h>
#include <lemon/dijkstra.h>
#include <lemon/adaptors.h>
#include <lemon/concepts/digraph.h>
#include <lemon/concepts/path.h>
#include <lemon/connectivity.h>
#include <tuple>
#include <set>
#include <lemon/preflow.h>
#include <lemon/lp.h>

using namespace std;
using namespace lemon;

const bool DEBUG = false; //if(DEBUG)
const bool DEBUG_CONDENSED = true;
const bool DEBUG_VALUE = true;

#define all(x) begin(x), end(x)
#define FOR(i, n) for (int i = 0; i < (n); ++i)

template <class C>
void Print_vector(const C &Original)
{
	for (const auto &v : Original)
	{
		cout << v << " ";
	}
	cout << endl;
}

class MultiCommodityProb
{

public:
	int vertex_numb_;
	int source_numb_;
	double all_flow_value;
	int number_of_arcs = 0;
	vector<pair<double, double>> vertex_points_;
	vector<vector<double>> base_columns;
	vector<double> base_solution;
	vector<double> dual_solution;
	vector<double> capacities_vectors;
	vector<double> w_row;
	lemon::ListDigraph graph_;
	lemon::ListDigraph::ArcMap<double> capacities_{graph_, false};
	vector<ListDigraph::Node> auxiliary_source_nodes_;

	MultiCommodityProb(int k, istream &in = std::cin) : source_numb_{k}, all_flow_value{0}, number_of_arcs{0}
	{
		ReadInput(in);
		AdditionalNodesEdge();
		for (ListDigraph::ArcIt arc(graph_); arc != INVALID; ++arc)
			++number_of_arcs;
		FillBaseColumns();

		int i = 0;
		capacities_vectors.resize(number_of_arcs);
		for (ListDigraph::ArcIt arc(graph_); arc != INVALID; ++arc)
			capacities_vectors[i++] = capacities_[arc];
		w_row.resize(number_of_arcs, 0);
	}

	void AddVertices(int n)
	{
		FOR(i, n)
		{
			graph_.addNode();
		}
	}

	template <typename T>
	double EuclidDist(T a, T b)
	{
		return sqrt((a.first - b.first) * (a.first - b.first) + (a.second - b.second) * (a.second - b.second));
	}

	void ReadInput(istream &in = std::cin)
	{
		int temp;
		in >> vertex_numb_;
		this->AddVertices(vertex_numb_);

		FOR(i, vertex_numb_)
		{
			int temp;
			in >> temp;
			double a, b;
			in >> a >> b;
			vertex_points_.push_back({a, b});
		}

		FOR(i, vertex_numb_)
		{
			FOR(j, vertex_numb_)
			{
				if (i < j)
				{

					ListDigraph::Arc t1 = graph_.addArc(graph_.nodeFromId(i), graph_.nodeFromId(j));
					capacities_[t1] = EuclidDist(vertex_points_[i], vertex_points_[j]);
					//ListDigraph::Arc t2 = graph_.addArc(graph_.nodeFromId(j), graph_.nodeFromId(i));
					//capacities_[t2] = EuclidDist(vertex_points_[i], vertex_points_[j]);
				}
			}
		}
	}

	ListDigraph::Arc FindArc(ListDigraph::Node from, ListDigraph::Node to)
	{
		ListDigraph::Arc temp;
		for (ListDigraph::OutArcIt a(graph_, from); a != INVALID; ++a)
		{
			if (graph_.target(a) == to)
			{
				temp = a;
				return temp;
			}
		}
	}

	void FillBaseColumns()
	{
		FOR(i, number_of_arcs)
		{
			vector<double> column;
			FOR(j, number_of_arcs)
			{
				if (i == j)
					column.push_back(1);
				else
					column.push_back(0);
			}
			base_columns.push_back(column);
		}
	}

	void AdditionalNodesEdge()
	{
		ListDigraph &g = graph_;
		int &k = source_numb_;
		FOR(i, k)
		{
			auxiliary_source_nodes_.push_back(graph_.addNode());
		}

		FOR(i, k)
		{
			double di = capacities_[FindArc(graph_.nodeFromId(i), graph_.nodeFromId(vertex_numb_ - i - 1))];
			all_flow_value = all_flow_value + 2 * di;
			capacities_[graph_.addArc(auxiliary_source_nodes_[i], graph_.nodeFromId(i))] = 2 * di;
		}
	}

	vector<double> LinearEquationSolver(vector<vector<double>> Columns, vector<double> c)
	{
		cout << endl
			 << "LOOKING FOR PRIMAL SOLUTION " << endl;
		vector<double> sol;
		Lp lp;
		vector<Lp::Col> x;

		FOR(i, (int)Columns.size())
		{
			x.push_back(lp.addCol());
		}
		FOR(i, (int)Columns.size())
		{
			lp.addRow(x[i] >= 0);
		}

		FOR(i, number_of_arcs)
		{
			if (DEBUG)
				cout << endl
					 << i << endl;
			Lp::Expr temp;
			FOR(j, (int)Columns.size())
			{
				temp += x[j] * Columns[j][i];
			}
			lp.addRow(temp == c[i]);
		}

		Lp::Expr maxNum;
		for (int i = number_of_arcs; i < (int)Columns.size(); ++i)
		{
			maxNum = maxNum + x[i];
		}
		lp.max();
		lp.obj(maxNum);

		lp.solve();

		if (lp.primalType() == Lp::OPTIMAL || lp.primalType() == Lp::FEASIBLE)
		{
			cout << "PRIMAL SOLUTION FOUND" << endl;
			FOR(i, (int)Columns.size())
			{
				sol.push_back(lp.primal(x[i]));
			}
		}
		else
		{
			cout << "NOT SOLVABLE\n";
		}
		return sol;
	}

	vector<double> DualSolution()
	{
		cout << endl
			 << "LOOKING FOR DUAL SOLUTION " << endl;
		cout << "Number of new columns: " << (int)base_columns.size() - number_of_arcs << endl;

		vector<double> sol;
		Lp lp;
		vector<Lp::Col> y;

		FOR(i, number_of_arcs)
		{
			y.push_back(lp.addCol());
		}

		for (int i = 0; i < (int)base_columns.size(); ++i)
		{
			Lp::Expr temp;
			FOR(j, number_of_arcs)
			{
				temp += y[j] * base_columns[i][j];
			}
			lp.addRow(temp >= w_row[i]);
		}

		Lp::Expr maxNum;
		FOR(i, number_of_arcs)
		{
			maxNum += y[i] * capacities_vectors[i];
		}
		lp.min();
		lp.obj(maxNum);

		lp.solve();

		if (lp.primalType() == Lp::OPTIMAL || lp.primalType() == Lp::FEASIBLE)
		{
			cout << "DUAL SOLUTION FOUND" << endl;
			int i = 0;
			for (ListDigraph::ArcIt arc(graph_); arc != INVALID; ++arc)
			{
				sol.push_back(lp.primal(y[i]));
				i++;
			}
		}
		else
		{
			cout << "NOT SOLVABLE\n";
		}
		return sol;
	}

	vector<double> ColumnGener(vector<ListDigraph::Node> &path)
	{
		vector<ListDigraph::Arc> arcs;
		for (int i = (int)path.size() - 1; i > 0; --i)
		{
			arcs.push_back(FindArc(path[i], path[i - 1]));
		}
		int ln = (int)arcs.size();
		vector<double> column;
		for (ListDigraph::ArcIt arc(graph_); arc != INVALID; ++arc)
		{
			bool exist = false;
			FOR(i, ln)
			{
				if (arc == arcs[i])
				{
					exist = true;
					break;
				}
			}
			if (exist)
			{
				column.push_back(1);
			}
			else
			{
				column.push_back(0);
			}
		}
		return column;
	}

	bool ShorterPath(vector<double> &dl)
	{
		cout << endl
			 << endl
			 << "CHECKING DUAL SOLUTION" << endl;
		ListDigraph &g = graph_;
		bool okay = true;
		FOR(i, source_numb_)
		{
			ListDigraph::Node si = auxiliary_source_nodes_[i];
			ListDigraph::Node ti = g.nodeFromId(vertex_numb_ - i - 1);
			ListDigraph::NodeMap<double> dist(g);
			ListDigraph::ArcMap<double> length(g);
			int j = 0;
			for (ListDigraph::ArcIt arc(graph_); arc != INVALID; ++arc)
			{
				length[arc] = dl[j++];
			}
			Dijkstra<ListDigraph, ListDigraph::ArcMap<double>>::Create
				dijkstra(g, length);
			dijkstra.distMap(dist);
			dijkstra.init();
			dijkstra.addSource(si);
			dijkstra.start();

			if (dijkstra.dist(ti) < 1)
			{
				vector<ListDigraph::Node> indexes;
				lemon::ListDigraph::Node curr = ti;
				while (curr != INVALID)
				{
					indexes.push_back(curr);
					// cout << "RECURSE: " << graph_.id(curr) << ", ";
					curr = dijkstra.predNode(curr);
				}

				cout << "New path: ";
				for (int l = 0; l < (int)indexes.size(); ++l)
				{
					cout << graph_.id(indexes[l]) << ", ";
				}

				base_columns.push_back(ColumnGener(indexes));
				w_row.push_back(1);
				okay = false;
				break;
			}
			if (!okay)
				break;
		}
		cout << endl
			 << "DUAL SOLUTION CHECKED, OUTCOME:" << okay << endl;
		return okay;
	}

	bool MCPWithColumnGeneration()
	{
		/*for (ListDigraph::ArcIt arc(graph_); arc != INVALID; ++arc)
		{
			cout << "arcid: " << graph_.id(arc) << "= " << graph_.id(graph_.source(arc))
				 << " to node " << graph_.id(graph_.target(arc)) << "cap: " << capacities_[arc] << ";";
		}
		cout << "\n\n\n";*/
		bool ready = false;
		while (!ready)
		{
			base_solution = LinearEquationSolver(base_columns, capacities_vectors);
			cout << "BASE SOLUTION: " << endl;
			cout << base_solution.size() << ' ';
			Print_vector(base_solution);

			dual_solution = DualSolution();
			cout << "DUAL SOLUTION: ";
			Print_vector(dual_solution);

			double solvalue = 0;
			for (int i = number_of_arcs; i < (int)base_columns.size(); i++)
			{
				solvalue = solvalue + base_solution[i];
			}
			cout << endl
				 << "Current value: " << solvalue << ". Goal:" << all_flow_value << "." << endl
				 << endl;

			ready = ShorterPath(dual_solution);
		}

		base_solution = LinearEquationSolver(base_columns, capacities_vectors);
		double solvalue = 0;
		for (int i = number_of_arcs; i < (int)base_columns.size(); i++)
		{
			solvalue = solvalue + base_solution[i];
		}

		Print_vector(base_solution);
		cout << endl
			 << "Current value: " << solvalue << ". Goal:" << all_flow_value << "." << endl
			 << endl;

		return 0;
	}
};

int main()
{
	ifstream fin("berlin52.txt");

	int k;
	cout << "Number of source nodes: ";
	cin >> k;
	cout << std::endl;

	MultiCommodityProb Test(k, fin);
	cout << Test.all_flow_value << endl;

	Test.MCPWithColumnGeneration();
}
