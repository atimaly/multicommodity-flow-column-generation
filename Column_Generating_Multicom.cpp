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
const bool DEBUG_CONDENSED = false;
const bool DEBUG_VALUE = true;
const long long int INF = 10000000000;

using ll = long long int;

#define all(x) begin(x), end(x)
#define FOR(i,n) for(int i = 0; i < (n); ++i)

template <class C>
void Print_vector(const C &Original) {
	for(const auto &v : Original) {
	    cout << v << " ";
	}
	cout << endl;
}

template <class C>
void Print_Matrix(const vector<vector<C>> &M, bool space = true) {
	for(int i = 0; i < (int)M.size(); ++i) {
		for(int j = 0; j < (int)M[i].size(); ++j) {
			cout << M[i][j]; if(space) cout << " ";
			}
	    cout << endl;
	}
}

template<class T, class C>
void Print_pair(const pair<T,C> &M) {
    cout << "(" << M.first << " , " << M.second << " ) ";
}

template<class T, class C>
void Print_Matrix_pair(const vector<vector<pair<T,C>>> &M) {
	for(int i = 0; i < (int)M.size(); ++i) {
		cout << i << ": ";
		for(int j = 0; j < (int)M[i].size(); ++j) {
			Print_pair(M[i][j]);
		}
	    cout << endl;
	}
}


class MultiCommodityProb{
		
	public:
		
		int vertex_numb_;
		int source_numb_;
		double all_flow_value;
		int number_of_arcs;
		vector<pair<double, double>> vertex_points_;
		vector<vector<double>> base_columns;
		vector<double> base_solution;
		vector<double> dual_solution;
		vector<double> capacities_vectors;
		vector<double> w_row;
		lemon::ListDigraph graph_;
		//lemon::ListDigraph::NodeMap<int> strongly_connected_comp_{graph_};   //ERROR azt hiszi fĂźggvĂŠny declarĂĄlok. () helyett {}-et kell tenni https://stackoverflow.com/questions/13734262/c-difference-between-function-declaration-and-object-initialization
		lemon::ListDigraph::ArcMap<double> capacities_{graph_, false};
		vector<ListDigraph::Node> auxiliary_source_nodes_;
		vector<ListDigraph::Node> auxiliary_sink_nodes_;
		
		
		MultiCommodityProb(int k, istream& in = std::cin): source_numb_{k}, all_flow_value{0}, number_of_arcs{0} {
			ReadInput(in);
			AdditionalNodesEdge();
			for(ListDigraph::ArcIt arc(graph_);arc!=INVALID;++arc) ++number_of_arcs;
			FillBaseColumns();
			
			int i = 0; capacities_vectors.resize(number_of_arcs);
			for(ListDigraph::ArcIt arc(graph_);arc!=INVALID;++arc) capacities_vectors[i++] = capacities_[arc];
			w_row.resize(number_of_arcs, 0);
		}
		
		void AddVertices(int n) {
			FOR(i,n) {
				graph_.addNode();
			}
		}
		
		template<typename T>
		double EuclidDist(T a, T b) {
			return sqrt((a.first-b.first)*(a.first-b.first) + (a.second-b.second)*(a.second-b.second));
		}
		
		void ReadInput(istream& in = std::cin)  {
			int temp;
			in >> vertex_numb_;
			this->AddVertices(vertex_numb_);
			
			FOR(i,vertex_numb_) {
				int temp; in >> temp;
				double a,b; in >> a >> b;
				vertex_points_.push_back({a,b});
			}
			
			FOR(i,vertex_numb_) {
				FOR(j, vertex_numb_) {
					if(i == j)
						continue;
					
					ListDigraph::Arc t1 = graph_.addArc(graph_.nodeFromId(i),graph_.nodeFromId(j));
					ListDigraph::Arc t2 = graph_.addArc(graph_.nodeFromId(j),graph_.nodeFromId(i));
					capacities_[t1] = EuclidDist(vertex_points_[i], vertex_points_[j]);
					capacities_[t2] = EuclidDist(vertex_points_[i], vertex_points_[j]);
					
				}
			}
			
		}
		
		ListDigraph::Arc FindArc(ListDigraph::Node from, ListDigraph::Node to) {
			ListDigraph::Arc temp;
			for (ListDigraph::OutArcIt a(graph_, from); a != INVALID; ++a) {
				if(graph_.target(a) == to) {temp == a; break;}
			}
			
			return temp;
		}
		
		void FillBaseColumns() {
			FOR(i,number_of_arcs) {
				vector<double> column; 
				FOR(j,number_of_arcs) {
					if(i == j) column.push_back(1);
					else column.push_back(0);
				}
				base_columns.push_back(column);
			}
		}
		
		void AdditionalNodesEdge() {
			ListDigraph &g = graph_;
			int &k = source_numb_;
			FOR(i,k) {
				auxiliary_source_nodes_.push_back(graph_.addNode());
			}
			/*
			FOR(i,k) {
				auxiliary_sink_nodes_.push_back(graph_.addNode());
			}*/
			
			FOR(i,k) {
				double di = capacities_[FindArc(g.nodeFromId(i), g.nodeFromId(vertex_numb_-i+1))];
				all_flow_value += di;
				capacities_[g.addArc(auxiliary_source_nodes_[i], g.nodeFromId(i))] = di;
				
				//capacities_[g.addArc(auxiliary_sink_nodes_[i], g.nodeFromId(vertex_numb_-i+1))] = di;
			}
		}
		
		vector<double> LinearEquationSolver(vector<vector<double>> Columns, vector<double> c) {
			vector<double> sol; 
			Lp lp;
			vector<Lp::Col> x;
			if(DEBUG) cout << "ZERO\n";
			FOR(i, (int)Columns.size()) {
				x.push_back(lp.addCol());
			}
			if(DEBUG) cout << "FIRST\n";
			FOR(i, (int)Columns.size()) {
				if(DEBUG) cout << endl << i << endl;
				Lp::Expr temp;
				FOR(j, (int)Columns.size()) {
					//if(DEBUG) cout << "COLUMNS value: " << Columns[j][i] << " " ;
					temp += x[i]*Columns[j][i];
				}
				lp.addRow(temp == c[i]);
			}
			if(DEBUG) cout << "SECOND\n";
			Lp::Expr maxNum; lp.addRow(maxNum == 0);
			lp.max();
			lp.obj(maxNum);
			lp.solve();
			
			if (lp.primalType() == Lp::OPTIMAL || lp.primalType() == Lp::FEASIBLE) {
				FOR(i, (int)Columns.size()) {
					sol.push_back(lp.primal(x[i]));
				}
			}
			else{
				cout << "NOT SOLVABLE\n";
			}
			
			return sol;
		}
		
		vector<double> DualSolution() {
			vector<double> sol; 
			Lp lp;
			vector<Lp::Col> x;
			if(DEBUG) cout << "ZERO\n";
			FOR(i, number_of_arcs) {
				x.push_back(lp.addCol());
			}
			if(DEBUG) cout << "FIRST\n";
			FOR(i,number_of_arcs) {
				if(DEBUG) cout << endl << i << endl;
				Lp::Expr temp;
				FOR(j, number_of_arcs) {
					//if(DEBUG) cout << "COLUMNS value: " << base_columns[j][i] << " " ;
					temp += x[i]*base_columns[j][i];
				}
				lp.addRow(temp >= w_row[i]);
			}
			if(DEBUG) cout << "SECOND\n";
			Lp::Expr maxNum;
			FOR(i,number_of_arcs) {
				maxNum += x[i]*capacities_vectors[i];
			}
			
			lp.min();
			lp.obj(maxNum);
			lp.solve();
			
			if (lp.primalType() == Lp::OPTIMAL || lp.primalType() == Lp::FEASIBLE) {
				FOR(i, number_of_arcs) {
					sol.push_back(lp.primal(x[i]));
				}
			}
			else{
				cout << "NOT SOLVABLE\n";
			}
			
			return sol;
		}
		
		
		vector<double> ColumnGener(vector<ListDigraph::Node> &path) {
			cout << "VAGYOK\n"<< endl;
			vector<ListDigraph::Arc> arcs;
			for(int i = (int)path.size(); i > 0; ++i) {
				arcs.push_back(FindArc(path[i], path[i-1]));
			}
			
			int ln = (int)arcs.size();
			vector<double> column;
			for(ListDigraph::ArcIt arc(graph_);arc!=INVALID;++arc) {
				bool exist = false;
				FOR(i,ln) {
					if(arc == arcs[i]) {
						exist = true;
						break;
					}
				}
				if(exist)
				 column.push_back(1);
				else column.push_back(0);
			}
		}
		
		bool ShorterPath(vector<double> &dl) {
			ListDigraph &g = graph_;
			cout << "VAGYOK\n"<< endl;
			bool okay = true;
			FOR(i,source_numb_) {
				ListDigraph::Node si = auxiliary_source_nodes_[i];
				ListDigraph::Node ti = g.nodeFromId(vertex_numb_-i+1);
				ListDigraph::NodeMap<double> dist(g);
				ListDigraph::ArcMap<double> length(g);
				int j = 0;
				for(ListDigraph::ArcIt arc(graph_);arc!=INVALID;++arc) length[arc] = dl[j++];
				Dijkstra<ListDigraph, ListDigraph::ArcMap<double>>
						  ::Create
						  dijkstra(g, length);
				//Dijkstra<ListGraph> dijkstra(g, length);
				dijkstra.distMap(dist);
				dijkstra.init();
				dijkstra.addSource(si);
				dijkstra.start();
				
				if(dijkstra.dist(ti) < 1) {
					cout << "VAGYOK\n"<< endl;
					vector<ListDigraph::Node> indexes;
					lemon::ListDigraph::Node curr = ti;
					while(curr != INVALID) {
						indexes.push_back(curr);
						curr = dijkstra.predNode(curr);
					}
					base_columns.push_back(ColumnGener(indexes));
					okay = false;
					break;
				}
			}
			return okay;
		}
		
		bool OneIterationOfGeneration() {
			base_solution = LinearEquationSolver(base_columns, capacities_vectors);
			if(DEBUG_VALUE) {cout << "BASE SOLUTION: \n"; Print_vector(base_solution);}
			dual_solution = DualSolution();
			if(DEBUG_VALUE) {cout << "DUAL SOLUTION: \n"; Print_vector(dual_solution);}
			bool okay = ShorterPath(dual_solution);
			return okay;			
		}
		
		
};



int main() {
	ifstream fin("berlin52.txt");
	
	int k = 10;
	MultiCommodityProb Test(k, fin);
	cout << Test.all_flow_value << endl;
	Test.OneIterationOfGeneration();
	/*
	vector<vector<double>> columns;
	columns.push_back(vector<double> {1, 0});
	columns.push_back(vector<double> {0, 1});
	vector<double> c{2,3};
	Print_vector(Test.LinearEquationSolver(columns, c));*/
}
