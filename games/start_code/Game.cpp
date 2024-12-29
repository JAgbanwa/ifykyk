//
// Created by Tim Apers on 29/10/2024.
//

#include "Game.h"

Game::Game(sf::RenderWindow* window) {
    this->window = window;
}

void Game::update() {
    setCurrentRoom();
    this->window->clear();
    if (currentRoom) { currentRoom->render(this->window); }
    this->window->display();
    while (window->isOpen()) {
        sf::Event event;

        // Wait for event to fire
        while (window->pollEvent(event)) {
            if (event.type == sf::Event::Closed) {
                window->close();
            } else if (event.type == sf::Event::KeyPressed) {
                currentRoom->update(&event);
                setCurrentRoom();
                this->window->clear();
                currentRoom->render(this->window);
                this->window->display();
            }
        }
    }

}

void Game::loadMap(const std::string& filename) {

}

void Game::setCurrentRoom() {

}