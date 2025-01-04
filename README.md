# lean-astar

A simple A* implementation in Lean4, made for Advent of Code 2023.

It currently is not formally validated, but might get validated later.

However, the termination of the pathfinding function has been shown, and it uses a formally validated binary heap for its open set, so the first steps towards formal validation have been done already.

Beware that this code is not optimized, and high performance is explicitly not a goal of this repo.