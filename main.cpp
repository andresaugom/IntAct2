/*
 * Integrated Activity 2: network planning for an Internet service company.
 * Reads a distance matrix, a capacity matrix and the coordinates of the
 * exchanges, and computes:
 *   1. Optimal fiber wiring (minimum spanning tree).
 *   2. Shortest delivery route visiting every neighborhood (TSP).
 *   3. Maximum data flow from the first to the last neighborhood.
 *   4. Voronoi polygon of each exchange (closest-exchange regions).
 *
 * Authors: <NAME_1> (<STUDENT_ID_1>), <NAME_2> (<STUDENT_ID_2>), <NAME_3> (<STUDENT_ID_3>)
 * Date: 2026-11-10
 */

#include <iostream>
#include <vector>
#include <queue>
#include <algorithm>
#include <climits>

typedef std::vector<std::vector<int>> Matrix;
typedef std::vector<std::pair<int, int>> Coords;
typedef std::pair<double, double> Point;
typedef std::vector<Point> Polygon;

// Large value that can still be added to a cost without overflowing an int.
const int INF_COST = INT_MAX / 2;

// Finds the vertex outside the tree with the smallest key.
// key: best known connection cost per vertex.
// inTree: true for vertices already in the tree.
// Returns the vertex index, or -1 if no reachable vertex is left.
int minKey(const std::vector<int>& key, const std::vector<bool>& inTree) {
	int minValue = INT_MAX;
	int minIndex = -1;
	for (unsigned int i = 0; i < key.size(); i++) {
		if (!inTree[i] && key[i] < minValue) {
			minValue = key[i];
			minIndex = i;
		}
	}
	return minIndex;
}

// Minimum spanning tree with Prim's algorithm on an adjacency matrix.
// A weight of 0 means there is no edge. O(n^2).
// n: number of vertices.
// adjMatrix: weighted adjacency matrix.
// edges: output list of the tree arcs (parent, child).
// Returns the total weight of the tree.
int mst(unsigned int n, const Matrix& adjMatrix,
		std::vector<std::pair<int, int>>& edges) {
	std::vector<int> key(n, INT_MAX);
	std::vector<int> parent(n, -1);
	std::vector<bool> inTree(n, false);
	int total = 0;
	unsigned int added = 0;
	int u = 0;

	key[0] = 0;

	// Stops early if the graph is disconnected (u == -1).
	while (added < n && u != -1) {
		u = minKey(key, inTree);
		if (u != -1) {
			inTree[u] = true;
			total += key[u];
			added++;
			if (parent[u] != -1) {
				edges.push_back({parent[u], u});
			}
			for (unsigned int v = 0; v < n; v++) {
				if (adjMatrix[u][v] != 0 && !inTree[v] && adjMatrix[u][v] < key[v]) {
					key[v] = adjMatrix[u][v];
					parent[v] = u;
				}
			}
		}
	}
	return total;
}

// Top-down DP with bitmasks: cheapest way to finish the tour from a state.
// mask: set of visited cities.
// curr: current city.
// cost: distance matrix.
// dp: memo table indexed [curr][mask], -1 when not computed yet.
// Returns the minimum cost to visit the remaining cities and return to city 0.
int totalCost(int mask, int curr, const Matrix& cost, Matrix& dp) {
	int n = cost.size();
	int answer = INF_COST;

	if (mask == (1 << n) - 1) {
		answer = cost[curr][0];
	} else if (dp[curr][mask] != -1) {
		answer = dp[curr][mask];
	} else {
		for (int i = 0; i < n; i++) {
			if ((mask & (1 << i)) == 0) {
				int candidate = cost[curr][i] + totalCost(mask | (1 << i), i, cost, dp);
				answer = std::min(answer, candidate);
			}
		}
		dp[curr][mask] = answer;
	}
	return answer;
}

// Rebuilds the optimal tour from the filled memo table, without a second table.
// cost: distance matrix.
// dp: memo table already filled by totalCost.
// route: output order of visit, starting and ending at city 0.
void buildRoute(const Matrix& cost, Matrix& dp, std::vector<int>& route) {
	int n = cost.size();
	int curr = 0;
	int mask = 1;

	route.push_back(0);
	while (mask != (1 << n) - 1) {
		int target = dp[curr][mask];
		int next = -1;
		for (int i = 0; i < n; i++) {
			if (next == -1 && (mask & (1 << i)) == 0 &&
				cost[curr][i] + totalCost(mask | (1 << i), i, cost, dp) == target) {
				next = i;
			}
		}
		route.push_back(next);
		mask |= 1 << next;
		curr = next;
	}
	route.push_back(0);
}

// Shortest closed route that visits every city exactly once. O(n^2 * 2^n).
// cost: distance matrix.
// route: output order of visit.
// Returns the cost of the route.
int tsp(const Matrix& cost, std::vector<int>& route) {
	int n = cost.size();
	Matrix dp(n, std::vector<int>(1 << n, -1));

	int best = totalCost(1, 0, cost, dp);
	buildRoute(cost, dp, route);
	return best;
}

// Breadth-first search for an augmenting path (Edmonds-Karp).
// residual: residual capacity matrix.
// src: source vertex.
// sink: target vertex.
// parent: output predecessor of each vertex on the path found.
// Returns true if the sink is reachable from the source.
bool bfs(const Matrix& residual, int src, int sink, std::vector<int>& parent) {
	int vertices = residual.size();
	std::vector<bool> visited(vertices, false);
	std::queue<int> pending;
	bool found = false;

	pending.push(src);
	visited[src] = true;
	parent[src] = -1;

	while (!pending.empty() && !found) {
		int u = pending.front();
		pending.pop();
		for (int v = 0; v < vertices; v++) {
			if (!visited[v] && residual[u][v] > 0) {
				visited[v] = true;
				parent[v] = u;
				pending.push(v);
				found = found || v == sink;
			}
		}
	}
	return found;
}

// Maximum flow from vertex 0 to vertex vertices - 1 with Ford-Fulkerson using
// BFS (Edmonds-Karp). O(V * E^2).
// vertices: number of vertices.
// flowMatrix: capacity matrix; it is modified into the residual graph.
// Returns the maximum flow value.
int maxFlow(int vertices, Matrix& flowMatrix) {
	int src = 0;
	int sink = vertices - 1;
	int totalFlow = 0;
	std::vector<int> parent(vertices, -1);

	while (bfs(flowMatrix, src, sink, parent)) {
		int pathFlow = INT_MAX;
		for (int v = sink; v != src; v = parent[v]) {
			pathFlow = std::min(pathFlow, flowMatrix[parent[v]][v]);
		}
		for (int v = sink; v != src; v = parent[v]) {
			flowMatrix[parent[v]][v] -= pathFlow;
			flowMatrix[v][parent[v]] += pathFlow;
		}
		totalFlow += pathFlow;
	}
	return totalFlow;
}

// Tells on which side of the perpendicular bisector of a and b a point lies.
// p: point to test.
// a: first exchange.
// b: second exchange.
// Returns a value <= 0 when p is at least as close to a as to b.
double bisectorSide(const Point& p, const Point& a, const Point& b) {
	return 2 * (b.first - a.first) * p.first
		+ 2 * (b.second - a.second) * p.second
		- (b.first * b.first + b.second * b.second
		- a.first * a.first - a.second * a.second);
}

// Clips a convex polygon, keeping only the area closer to a than to b
// (Sutherland-Hodgman against one half-plane).
// polygon: convex polygon to clip.
// a: exchange whose side is kept.
// b: exchange whose side is discarded.
// Returns the clipped polygon, empty if nothing remains.
Polygon clipPolygon(const Polygon& polygon, const Point& a, const Point& b) {
	const double EPSILON = 1e-9;
	Polygon result;

	if (!polygon.empty()) {
		Point prev = polygon.back();
		double prevValue = bisectorSide(prev, a, b);

		for (const Point& curr : polygon) {
			double currValue = bisectorSide(curr, a, b);
			bool prevInside = prevValue <= EPSILON;
			bool currInside = currValue <= EPSILON;

			// The edge crosses the bisector, so add the crossing point.
			if (prevInside != currInside) {
				double t = prevValue / (prevValue - currValue);
				result.push_back({prev.first + t * (curr.first - prev.first),
					prev.second + t * (curr.second - prev.second)});
			}
			if (currInside) {
				result.push_back(curr);
			}
			prev = curr;
			prevValue = currValue;
		}
	}
	return result;
}

// Builds the bounding rectangle that stands in for the unbounded cells.
// points: exchange locations.
// Returns the rectangle, larger than the points by ten times their spread.
Polygon boundingBox(const std::vector<Point>& points) {
	double minX = points[0].first;
	double maxX = points[0].first;
	double minY = points[0].second;
	double maxY = points[0].second;

	for (const Point& p : points) {
		minX = std::min(minX, p.first);
		maxX = std::max(maxX, p.first);
		minY = std::min(minY, p.second);
		maxY = std::max(maxY, p.second);
	}

	double margin = std::max({maxX - minX, maxY - minY, 1.0}) * 10.0;
	return {{minX - margin, minY - margin}, {maxX + margin, minY - margin},
		{maxX + margin, maxY + margin}, {minX - margin, maxY + margin}};
}

// Builds the Voronoi cell of every exchange by clipping the bounding box
// against the bisector with each other exchange. O(n^2 * n).
// sites: exchange coordinates.
// Returns one polygon per exchange, in input order.
std::vector<Polygon> voronoi(const Coords& sites) {
	std::vector<Point> points;
	std::vector<Polygon> polygons;

	for (const auto& [x, y] : sites) {
		points.push_back({double(x), double(y)});
	}

	for (unsigned int i = 0; i < points.size(); i++) {
		Polygon cell = boundingBox(points);
		for (unsigned int j = 0; j < points.size(); j++) {
			if (i != j) {
				cell = clipPolygon(cell, points[i], points[j]);
			}
		}
		polygons.push_back(cell);
	}
	return polygons;
}

// Reads a square matrix of size n x n from standard input.
// n: matrix dimension.
// Returns the matrix read.
Matrix readMatrix(int n) {
	Matrix matrix(n, std::vector<int>(n, 0));
	for (auto& row : matrix) {
		for (int& value : row) {
			std::cin >> value;
		}
	}
	return matrix;
}

// Reads n points written as "(x,y)" from standard input.
// n: number of points.
// Returns the list of coordinates.
Coords readPoints(int n) {
	Coords points(n);
	char separator = ' ';
	for (auto& [x, y] : points) {
		std::cin >> separator >> x >> separator >> y >> separator;
	}
	return points;
}

// Prints output 1: the fiber wiring arcs, named A, B, C...
// edges: arcs of the minimum spanning tree.
void printWiring(const std::vector<std::pair<int, int>>& edges) {
	std::cout << "1. Wiring:" << std::endl;
	for (const auto& [a, b] : edges) {
		std::cout << "(" << char('A' + a) << "," << char('A' + b) << ")" << std::endl;
	}
	std::cout << std::endl;
}

// Prints output 2: the delivery route as city letters.
// route: order of visit, starting and ending at the same city.
void printRoute(const std::vector<int>& route) {
	std::cout << "2. Route:" << std::endl;
	for (size_t k = 0; k < route.size(); k++) {
		std::cout << char('A' + route[k]);
		if (k + 1 < route.size()) {
			std::cout << " -> ";
		}
	}
	std::cout << std::endl << std::endl;
}

// Prints output 4: one polygon per exchange.
// polygons: Voronoi cells in the same order as the exchanges.
void printPolygons(const std::vector<Polygon>& polygons) {
	std::cout << "4. Polygons:" << std::endl;
	for (unsigned int i = 0; i < polygons.size(); i++) {
		std::cout << char('A' + i) << ": ";
		for (const Point& p : polygons[i]) {
			std::cout << "(" << p.first << "," << p.second << ") ";
		}
		std::cout << std::endl;
	}
}

int main() {
	std::ios::sync_with_stdio(false);
	std::cin.tie(nullptr);

	int n = 0;
	std::cin >> n;

	Matrix distanceMatrix = readMatrix(n);
	Matrix capacityMatrix = readMatrix(n);
	Coords exchanges = readPoints(n);

	std::vector<std::pair<int, int>> edges;
	mst(n, distanceMatrix, edges);
	printWiring(edges);

	std::vector<int> route;
	tsp(distanceMatrix, route);
	printRoute(route);

	std::cout << "3. Maximum flow:" << std::endl;
	std::cout << maxFlow(n, capacityMatrix) << std::endl << std::endl;

	printPolygons(voronoi(exchanges));

	return 0;
}
