#include <iostream>
#include <vector>
typedef std::vector<unsigned int> VU;
typedef std::vector<VU> VVU;
#include <random>

std::default_random_engine generator;

void fill(VVU &lts, unsigned int root, unsigned int size) {
  std::uniform_int_distribution<unsigned int> distribution(0,size - 1);
  unsigned int left_subtree_size(distribution(generator));
  if (left_subtree_size > 0) {
    fill(lts, root + 1, left_subtree_size);
    lts[root - 1].push_back(root + 1);
  }
  if (left_subtree_size < size - 1) {
    fill(lts, root + 1 + left_subtree_size, size - 1 - left_subtree_size);
    lts[root - 1].push_back(root + 1 + left_subtree_size);
  }
}

int main() {
  unsigned int n(20);
  VVU lts(n);
  fill(lts, 1, n);
  std::cout << "digraph {" << std::endl;
  for (unsigned int i1(1); i1 <= n; ++i1) 
    for (unsigned int i2(1); i2 <= lts[i1 - 1].size(); ++i2) 
      std::cout << i1 << " -> " << lts[i1 - 1][i2 - 1] << " [\"action\" = 0]" << std::endl;
  std::cout << "}" << std::endl;
  return 0;
}
