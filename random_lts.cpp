#include <iostream>
#include <vector>
typedef std::vector<unsigned int> VU;
typedef std::vector<VU> VVU;
#include <random>
#include <chrono>

std::default_random_engine generator(std::chrono::system_clock::now().time_since_epoch().count());

void fill(VVU &lts, unsigned int root, unsigned int size, VU &leaves) {
  if (size <= 1)
    leaves.push_back(root);
  else {
    std::uniform_int_distribution<unsigned int> distribution(0,size - 1);
    unsigned int left_subtree_size(distribution(generator));
    if (left_subtree_size > 0) {
      fill(lts, root + 1, left_subtree_size, leaves);
      lts[root - 1].push_back(root + 1);
    }
    if (left_subtree_size < size - 1) {
      fill(lts, root + 1 + left_subtree_size, size - 1 - left_subtree_size, leaves);
      lts[root - 1].push_back(root + 1 + left_subtree_size);
    }
  }
}

int main() {
  unsigned int n(10);
  unsigned int buffer(10);
  VVU lts(n);
  VU leaves;
  fill(lts, 1, n, leaves);
  std::cout << "digraph {" << std::endl; {
    std::uniform_int_distribution<unsigned int> distribution(1,leaves.size());
    lts[leaves[distribution(generator) - 1] - 1].push_back(1);
  }
  for (unsigned int i1(1); i1 <= n; ++i1) 
    for (unsigned int i2(1); i2 <= lts[i1 - 1].size(); ++i2) 
      std::cout << (buffer + i1) << " -> " << (buffer + lts[i1 - 1][i2 - 1]) << " [\"action\" = 0]" << std::endl;
  std::cout << "}" << std::endl;
  return 0;
}
