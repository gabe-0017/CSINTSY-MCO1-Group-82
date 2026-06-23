package solver;

import java.util.*;

public class SokoBot {

  /* -0-0-0-0-0-0-0-0-0-0- FUNCTIONS -0-0-0-0-0-0-0-0-0-0- */

  /**
   * solveSokobanPuzzle
   * parses the map into usable structures and runs A* to find a solution.
   * @param width     number of columns in the level
   * @param height    number of rows in the level
   * @param mapData   2D char array of static elements
   * @param itemsData 2D char array of moving elements
   * @return          solution string of moves, or empty string if unsolvable
   */
  public String solveSokobanPuzzle(int width, int height, char[][] mapData, char[][] itemsData) {
    // collect map info
    boolean[][] walls = new boolean[height][width];
    boolean[][] targets = new boolean[height][width];
    boolean[][] deadCells = new boolean[height][width];

    List<int[]> targetList = new ArrayList<>();

    // parse static map elements into walls and targets arrays
    for (int r = 0; r < height; r++)
      for (int c = 0; c < width; c++) {
        if (mapData[r][c] == '#') // mark wall cells
          walls[r][c] = true;
        if (mapData[r][c] == '.') { // mark target cells
          targets[r][c] = true;
          targetList.add(new int[]{r,c});
        }
      }

    computeDeadCells(deadCells, walls, targets, height, width);

    // build initial state
    int playerR = -1, playerC = -1;
    List<long[]> initBoxes = new ArrayList<>();

    // parse moving elements to find the player and box starting positions
    for (int r = 0; r < height; r++)
      for (int c = 0; c < width; c++) {
        if (itemsData[r][c] == '@') { // found the player
          playerR = r;
          playerC = c;
        }
        if (itemsData[r][c] == '$') // found a box, record its position
          initBoxes.add(new long[]{r,c});
      }

    long[] boxArr = new long[initBoxes.size()];

    for (int i = 0; i < initBoxes.size(); i++) // pack box positions into a single long array
      boxArr[i] = pack(initBoxes.get(i)[0], initBoxes.get(i)[1]);

    // sort boxes for consistent state hashing, then run A*
    Arrays.sort(boxArr);
    State initial = new State(playerR, playerC, boxArr, "");
    String result = aStar(initial, walls, targets, targetList, deadCells, height, width);

    if (result == null) { // no solution found...
      return ""; // ...return empty string
    } else { // solution found...
      return result; // ...return the move sequence
    }
  }

  /**
   * aStar
   * runs A* search over the Sokoban state space to find an optimal sequence of moves.
   * @param initial    the starting state
   * @param walls      2D boolean array marking wall cells
   * @param targets    2D boolean array marking target cells
   * @param targetList flat list of target coordinates for heuristic computation
   * @param deadCells  2D boolean array of statically unreachable cells (see computeDeadCells)
   * @param height     number of rows in the level
   * @param width      number of columns in the level
   * @return           solution move string, or null if no solution exists
   */
  private String aStar(State initial, boolean[][] walls, boolean[][] targets,
                       List<int[]> targetList, boolean[][] deadCells, int height, int width) {

    int d, nr, nc, br, bc, newG;
    long hash;
    int boxIdx;
    long[] newBoxes;
    State cur;
    Integer best;
    // Direction Vectors (up, down, left, right)
    int[] dr = {-1, 1, 0, 0};
    int[] dc = {0, 0, -1, 1};
    char[] dirChar = {'u','d','l','r'};
    // Open list: states to explore, ordered by f (starting with the lowest)
    PriorityQueue<State> open = new PriorityQueue<>(Comparator.comparingInt(s -> s.f));
    Map<Long, Integer> visited = new HashMap<>();

    // Initializing the starting state and add it to the open list
    initial.g = 0;
    initial.h = heuristic(initial.boxes, targetList);
    initial.f = initial.h;
    open.add(initial);

    while (!open.isEmpty()) { // Continue exploring until no states are left
      cur = open.poll(); // Pick the most promising state (lowest f)

      // Check if all boxes are in target cells already, return the viable solution
      if (isGoal(cur.boxes, targets))
        return cur.path;

      hash = stateHash(cur);
      best = visited.get(hash);

      if (best != null && best <= cur.g) // Skip if already visited this state with a better or equal cost
        continue;

      visited.put(hash, cur.g);

      // Try all four directions
      for (d = 0; d < 4; d++) { // Generating a neighbor state for each direction
        nr = cur.playerR + dr[d];
        nc = cur.playerC + dc[d];

        // Skip Conditions
        if (nr < 0 || nr >= height || nc < 0 || nc >= width) // Out of bounds
          continue;
        if (walls[nr][nc]) // Next cell is a wall
          continue;

        boxIdx = findBox(cur.boxes, nr, nc);
        newBoxes = cur.boxes;

        if (boxIdx >= 0) { // Next cell has a box, attempt to push it

          // Pushes a box
          br = nr + dr[d];
          bc = nc + dc[d];

          // Skip Conditions
          if (br < 0 || br >= height || bc < 0 || bc >= width) // Destination is out of bounds
            continue;
          if (walls[br][bc]) // Destination is a wall
            continue;
          if (findBox(cur.boxes, br, bc) >= 0) // Another box is at destination
            continue;
          if (deadCells[br][bc] && !targets[br][bc]) // Destination is a dead cell
            continue;

          newBoxes = cur.boxes.clone();
          newBoxes[boxIdx] = pack(br, bc);
          Arrays.sort(newBoxes);

          // Skip if push causes a deadlock
          if (isFrozenDeadlock(newBoxes, walls, targets, br, bc, height, width))
            continue;
        }

        newG = cur.g + 1;
        State next = new State(nr, nc, newBoxes, cur.path + dirChar[d]);
        next.g = newG;
        next.h = heuristic(newBoxes, targetList);
        next.f = newG + next.h;

        long nextHash = stateHash(next);
        Integer nextBest = visited.get(nextHash);

        // Skip if already found a better or equal path to this state
        if (nextBest != null && nextBest <= newG)
          continue;

        open.add(next); // Add neighbor to open list for future exploration
      }
    }
    return null; // If the program exits the while-loop, there is no solution; return null
  }

  /**
   * heuristic
   * estimates remaining cost as the sum of each box's distance to its nearest target.
   * @param boxes   sorted array of packed box positions
   * @param targets list of target coordinates
   * @return        estimated number of moves still needed
   */
  private int heuristic(long[] boxes, List<int[]> targets) {
    int total = 0;

    for (long b : boxes) { // find the closest target for each box
      int br = row(b), bc = col(b);
      int minDist = Integer.MAX_VALUE;

      for (int[] t : targets) { // compute the distance to each target
        int d = Math.abs(br - t[0]) + Math.abs(bc - t[1]);

        if (d < minDist) // update if the target is closer
          minDist = d;
      }
      total += minDist; // add the closest distance to the current total
    }
    return total; // return the sum of each box's closest distance to a target
  }

  /**
   * computeDeadCells
   * pre-computes which cells are statically dead (a box there can never reach any target).
   * @param dead    output array; dead[r][c] is set to true if the cell is a dead cell
   * @param walls   2D boolean array marking wall cells
   * @param targets 2D boolean array marking target cells
   * @param height  number of rows in the level
   * @param width   number of columns in the level
   * @return        void (results written into dead[][])
   */
  private void computeDeadCells(boolean[][] dead, boolean[][] walls,
                                boolean[][] targets, int height, int width) {

    /*
    "Live" cell characteristics:
      1. The bot can push a box from that cell
      2. There exists some sequence of pushes that gets that box to a target
    "Dead" cell example: corner cells (bot cannot push the box out anymore)
    */
    // compute live cells using reverse BFS
    boolean[][] live = new boolean[height][width];
    Queue<long[]> queue = new LinkedList<>();

    // target cells are always live...
    for (int r = 0; r < height; r++)
      for (int c = 0; c < width; c++)
        if (targets[r][c]) { // ...so we seed the BFS from target cells
          live[r][c] = true;
          queue.add(new long[]{r,c});
        }

    int[] dr = {-1,1,0,0};
    int[] dc = {0,0,-1,1};

    while (!queue.isEmpty()) {
      long[] cur = queue.poll();
      int r = (int)cur[0], c = (int)cur[1];

      for (int d = 0; d < 4; d++) {
        int br = r - dr[d];
        int bc = c - dc[d]; // where box was
        int pr = br - dr[d];
        int pc = bc - dc[d]; // where player was

        if (br < 0 || br >= height || bc < 0 || bc >= width) // skip if box origin is out of bounds
          continue;
        if (pr < 0 || pr >= height || pc < 0 || pc >= width) // skip if player position is out of bounds
          continue;
        if (walls[br][bc] || walls[pr][pc]) // skip if box-origin/player-position is a wall (push impossible)
          continue;
        if (!live[br][bc]) { // not yet visited, mark it live and explore it next
          live[br][bc] = true;
          queue.add(new long[]{br, bc});
        }
      }
    }

    for (int r = 0; r < height; r++)
      for (int c = 0; c < width; c++)
        if (!walls[r][c]) // wall cells are never dead or live...
          dead[r][c] = !live[r][c]; // ...so we only mark non-wall cells as dead cells
  }

  /**
   * isFrozenDeadlock
   * checks whether the newly pushed box causes a 2x2 block to freeze deadlock.
   * A freeze deadlock is a 2x2 block where every cell is a wall or box, and at least one box is not on a target.
   * @param boxes   current sorted array of packed box positions
   * @param walls   2D boolean array marking wall cells
   * @param targets 2D boolean array marking target cells
   * @param br      row of the newly pushed box
   * @param bc      column of the newly pushed box
   * @param height  number of rows in the level
   * @param width   number of columns in the level
   * @return        true if a freeze deadlock is detected, false otherwise
   */
  private boolean isFrozenDeadlock(long[] boxes, boolean[][] walls, boolean[][] targets,
                                   int br, int bc, int height, int width) {
    // check all 2x2 squares containing (br,bc)
    int[] offR = {0, 0, -1, -1};
    int[] offC = {0, -1, 0, -1};

    for (int k = 0; k < 4; k++) {
      int r0 = br + offR[k];
      int c0 = bc + offC[k];

      if (r0 < 0 || r0+1 >= height || c0 < 0 || c0+1 >= width) // skip if 2x2 block is out of bounds
        continue;

      // check 2x2 block (r0,c0),(r0,c0+1),(r0+1,c0),(r0+1,c0+1)
      boolean allBlocked = true;
      boolean hasBox = false;
      boolean allOnTarget = true;

      for (int dr2 = 0; dr2 <= 1; dr2++) {
        for (int dc2 = 0; dc2 <= 1; dc2++) {
          int rr = r0+dr2, cc = c0+dc2;
          boolean isWall = walls[rr][cc];
          boolean isBox  = findBox(boxes, rr, cc) >= 0;

          if (!isWall && !isBox) { // found an empty cell, so no need to check remaining cells (1)
            allBlocked = false;
            break; // break out of loop since puzzle is not frozen yet (1)
          }
          // if no empty cell is found, the bot is surrounded by wall/box cells
          if (isBox) { // found a box cell, now check if it's on a target
            hasBox = true;
            if (!targets[rr][cc]) // box is not on a target, so this block is unsolvable
              allOnTarget = false;
          }
        }
        if (!allBlocked) // found an empty cell, so no need to check remaining cells (2)
          break; // break out of loop since puzzle is not frozen yet (2)
      }
      // deadlock check: if every cell is a wall/box, and at least one box is not on a target...
      if (allBlocked && hasBox && !allOnTarget)
        return true; // ...then the puzzle is deadlocked (no possible solution)
    }
    // if program successfully exits the for-loop...
    return false; // ...then the puzzle is not deadlocked (possible solution)
  }

  /* -0-0-0-0-0-0-0-0-0-0- HELPERS -0-0-0-0-0-0-0-0-0-0- */

  /**
   * isGoal
   * checks whether all boxes are on target cells.
   * @param boxes   sorted array of packed box positions
   * @param targets 2D boolean array marking target cells
   * @return        true if puzzle is solved, false otherwise
   */
  private boolean isGoal(long[] boxes, boolean[][] targets) {
    for (long b : boxes)
      if (!targets[row(b)][col(b)])
        return false;
    return true;
  }

  /**
   * findBox
   * searches the boxes array for a box at the given coordinates.
   * @param boxes sorted array of packed box positions
   * @param r     row to search
   * @param c     column to search
   * @return      index of the box in the array, or -1 if not found
   */
  private int findBox(long[] boxes, int r, int c) {
    long key = pack(r, c);
    for (int i = 0; i < boxes.length; i++)
      if (boxes[i] == key)
        return i;
    return -1;
  }

  /**
   * pack
   * encodes a (row, col) pair into a single long value for compact storage and hashing.
   * @param r row coordinate
   * @param c column coordinate
   * @return  encoded long value
   */
  private long pack(long r, long c) {
    return r * 1000 + c;
  }

  /**
   * row
   * extracts the row from a packed coordinate.
   * @param p packed coordinate
   * @return  row value
   */
  private int row(long p) {
    return (int)(p / 1000);
  }

  /**
   * col
   * extracts the column from a packed coordinate.
   * @param p packed coordinate
   * @return  column value
   */
  private int col(long p) {
    return (int)(p % 1000);
  }

  /**
   * stateHash
   * produces a single long hash representing the full game state.
   * @param s the state to hash
   * @return  hash value of the state
   */
  private long stateHash(State s) {
    long h = s.playerR * 1000L + s.playerC;
    for (long b : s.boxes)
      h = h * 1_000_003L + b;
    return h;
  }

  /* -0-0-0-0-0-0-0-0-0-0- STATE CLASS -0-0-0-0-0-0-0-0-0-0- */

  /**
   * State
   * represents a single snapshot of the game at a point in time.
   * Stores; [1] the player's position, [2] all box positions, [3] the move path taken to reach this state,
   * and [4] the A* cost values used to prioritize exploration.
   *
   * @field playerR - current row  of the player [1]
   * @field playerC - current column of the player [1]
   * @field boxes   - sorted array of packed box positions (see pack()) [2]
   * @field path    - sequence of moves taken from the initial state to reach this one [3]
   * @field g       - actual cost (number of moves taken so far) [4]
   * @field h       - estimated cost to goal (heuristic) [4]
   * @field f       - total estimated cost (f = g + h) [4]
   */
  private static class State {
    int playerR, playerC;
    long[] boxes;
    String path;
    int g, h, f;

    State(int pr, int pc, long[] boxes, String path) {
      this.playerR = pr; this.playerC = pc;
      this.boxes = boxes; this.path = path;
    }
  }
}
