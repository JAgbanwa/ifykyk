//
// Created by Tim Apers on 29/10/2024.
//

#ifndef ENTITY_H
#define ENTITY_H

#include <SFML/Graphics.hpp>

struct Position {
    int x;
    int y;
};

class Entity {
public:
    virtual void update(sf::Event* event);

    // Onderstaande functies niet aanpassen!
    void setSprite(const std::string &img_path);
    void render(sf::RenderWindow *painter);
    ~Entity() = default;

private:
    Position position;
    sf::Sprite sprite;
    sf::Texture texture;
};


class Player : public Entity {
public:
    void update(sf::Event* event) override;
};

class Weapon : public Entity {};

class Wall : public Entity {};

class Floor : public Entity {};

class Enemy : public Entity {};

#endif //ENTITY_H
